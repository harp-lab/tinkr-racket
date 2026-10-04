

A Racket prototype for tinkr-lang version 0.

The goal of this prototype is to be correct and reasonably implemented for all correct inputs. We'll perform only minimal optimizations and focus on having a reasonable baseline for debugging, writing a self-hosting tinkr compiler in tinkr, and for prototyping new features and stack implementations.

Only a few tests are currently working. Stay tuned.


## Build Instructions

This project requires a few dependencies which can be installed with:

```
sudo apt-get install libgc-dev
sudo apt-get install libgmp-dev
sudo apt-get install lld
```

- Try running `racket test/test.rkt test/new_tests/if.ti`
  - Note: `test/test.rkt` has a few helpful command line options.
- Run `/tmp/ti/out.bin` to execute the compiled program.
- Build info can be found in the `/tmp/ti` directory.
- Run all tests with `python test/test.py -a`. Run the script with `-h` option for more options.

## Work in Progress

- Inlining pass not fully working yet for all test cases (see the `inlining` branch): test cases with closures are broken.
- Algebraic effects not implemented.
- `patterns1` test case failing.
- Expect other bugs.
