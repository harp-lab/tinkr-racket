"""
Module to test the tinkr compiler while all phases are not complete.
"""

import argparse
import os
from subprocess import PIPE, STDOUT, Popen, TimeoutExpired

TIMEOUT = 240
LONG_TESTS = []
KNOWN_FAILING_TESTS = ["patterns1", "patterns3", "str"]
BLACKLIST = ["test.py", "test.rkt", "files",
             "tests", # only keep new_tests for now

             # opperators #, ->, <- not working yet and seem to stall/crash the tester
             "if7", "if8", "if9",
             "list3", "prompt_yield0", "prompt_yield1",
             "unique_escape", "unique0",
             
             # new operator also stalls the tester
             "new0", "new1", "new2",
             
             # other test cases that stall the tester
             "set2", "set3"]

PATH = os.path.abspath(os.path.dirname(__file__))
PATH_TO_TI_DIR = os.path.join("/tmp", "ti")
PATH_TO_TESTER_FILE = os.path.join(PATH, "test.rkt")
PATH_TO_BINARY = os.path.join(PATH_TO_TI_DIR, "out.bin")
PATH_TO_ERROR_LOG = os.path.join(PATH_TO_TI_DIR, "error.log")

TEST_DIR_TESTS = "tests"
TEST_DIR_NEW_TESTS = "new_tests"
TEST_DIRS = [TEST_DIR_TESTS, TEST_DIR_NEW_TESTS]

def _test_compiler(file, tests, racket_path):
    b_stdout, _, _ = runcmdsafe(
        f'"{racket_path}" "{PATH_TO_TESTER_FILE}" "{file}"'
    )

    # Invoke X86 output binary.
    if os.path.exists(PATH_TO_BINARY):
        stdout, _, _ = runcmdsafe(f"{PATH_TO_BINARY}")
    else:
        print("Error: Output binary not found.")
        if os.path.exists(PATH_TO_ERROR_LOG):
            with open(PATH_TO_ERROR_LOG, "r") as error_log:
                error_content = error_log.read()
                print(f"Error log content:\n{error_content}")

        print("~~~~~~~~~~~~~~~~~~")
        print(f"Output:\n{b_stdout.decode('utf-8')}")
        return "ERROR"

    # Return decoded output.
    return stdout.decode("utf-8")

def runcmdsafe(binfile, dir="."):
    b_stdout, b_stderr, b_exitcode = runcmd(binfile, dir)

    return b_stdout, b_stderr, b_exitcode


def runcmd(cmd, dir="."):
    stdout, stderr = None, None
    if os.name != "nt":
        cmd = "exec " + cmd
    with Popen(
        cmd, shell=True, stdin=PIPE, stdout=PIPE, stderr=STDOUT, close_fds=True, cwd=dir
    ) as process:
        try:
            stdout, stderr = process.communicate(timeout=TIMEOUT)
        except TimeoutExpired:
            if os.name == "nt":
                Popen("TASKKILL /F /PID {pid} /T".format(pid=process.pid))
            else:
                process.kill()
                exit()
    return stdout, stderr, process.returncode


def assertequals(expected, actual):
    if expected == actual:
        passtest()
        return True
    else:
        failtest(
            f"--- Expected ---\n{expected}\n----------------\n--- Received ---\n{actual}\n---------------"
        )
        return False


def failtest(message):
    print("        FAILED")
    print(message)


def passtest():
    print("     PASSED")


def runtest(
    name, tests, racket_path, iterations=1, quick=False, use_assert=False
):
    """
    Runs the given test a number of times and specifies the result.

    Args:
        name: The name of the test to run (which should match a
        tests: The name of the tests directory.
        folder in the "tests" directory).
        iterations: The number of times to run the test. (Optional)
        quick: Whether or not to exclude long-running tests. (Optional)
    Returns:
        A boolean indicating if the test was successful or not.
    """
    if name in BLACKLIST:
        print(f"Skipping blacklisted test: {name}")
        return True

    ext = "ti"

    if quick and name in LONG_TESTS:
        return True
    # Read the expected answer.
    answer_path = os.path.join(PATH, tests, name, "answer")
    with open(answer_path, "r") as answer_f:
        answer = answer_f.read()
    ret = True
    for _ in range(0, iterations):
        print("---------------------")
        print(f"\nRunning test: {name}")
        test_path = os.path.join(PATH, tests, name, f"{name}.{ext}")
        ret = assertequals(answer, _test_compiler(test_path, tests, racket_path))

    # For github actions/pytest
    if use_assert:
        assert ret == True
    return ret


def run_all_tests(racket_path, iterations=1, quick=False, use_assert=False):
    """Wrapper to run all tests."""
    run_compiler_tests(
        racket_path,
        list_all_tests(),
        iterations,
        quick,
        use_assert,
    )

def run_compiler_tests(
    racket_path, tests, iterations=1, quick=False, use_assert=False
):
    """
    Runs all tests a given number of times and provides a summary.

    Args:
      racket_path: The path to racket on the system.
      tests: The list of tests to run.
      iterations: The number of times to run the test. (Optional)
      quick: Whether or not to exclude long-running tests. (Optional)
      use_assert: Whether or not to use asserts during testing. (Optional)
    """
    num_passed = 0
    tests_skipped = 0

    for test in tests:
        if quick and test[0] in LONG_TESTS:
            tests_skipped += 1
        elif runtest(
            test[0],
            test[1],
            racket_path,
            iterations=iterations,
            quick=quick,
            use_assert=use_assert,
        ):
            num_passed += 1

    print("\n===========================")
    print(f"Summary: {num_passed} / {len(tests) - tests_skipped} tests passed")
    print("===========================")


def list_all_tests():
    """
    Gathers a list of all the available tests.

    Returns:
      tests: The sorted paths of the available tests
    """
    tests = []
    for test_dir in TEST_DIRS:
        if test_dir in BLACKLIST:
            print(f"Skipping blacklisted test directory: {test_dir}")
            continue

        tests += [
            (test, test_dir)
            for test in os.listdir(os.path.join(PATH, test_dir))
            if not test.startswith(".") and not test in BLACKLIST
        ]

    tests.sort()
    return tests

def main():
    """
    Processes command line arguments and calls the appropriate testing functions.
    """
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--list", "-l", help="List available tests", action="store_true"
    )
    parser.add_argument("--all", "-a", help="Perform all tests", action="store_true")
    parser.add_argument(
        "--test", "-t", nargs="*", type=str, help="Perform a specific testname (case sensitive; can pass multiple test names)"
    )
    parser.add_argument(
        "--ignore_failing", "-f", help="Ignore known failing test cases", action="store_true"
    )
    parser.add_argument(
        "--iterations",
        "-i",
        type=int,
        help="Perform the test(s) a given number of times",
    )
    parser.add_argument(
        "--racket_path", "-r", type=str, help="Give an path to racket binary."
    )
    args = parser.parse_args()

    iters = 1
    if args.iterations:
        iters = args.iterations

    racket_path = "racket"

    if args.racket_path:
        racket_path = args.racket_path

    if args.ignore_failing:
        BLACKLIST.extend(KNOWN_FAILING_TESTS)

    if args.all:
        run_all_tests(racket_path, iters, quick=False)
        return

    if args.test:
        all = list_all_tests()
        for test in args.test:
            if test not in [test[0] for test in all]:
                print(f"Error: test {test} does not exist.")
                continue
            
            test_dir = all[[test[0] for test in all].index(test)][1]

            path = os.path.abspath(os.path.join(PATH, test_dir, test))
            tests = test_dir
            if not os.path.exists(path):
                print(f"Error: test {test} does not exist.")
                continue

            runtest(test, tests, racket_path, iters, quick=False)
            continue
        return

    if args.list:
        print("Available tests: ")
        print(*(list_all_tests()), sep="\n")
        return

    parser.print_help()


if __name__ == "__main__":
    main()
