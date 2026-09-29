def compose(f, g):
    return lambda x: f(g(x))

def make_adder(n):
    return lambda x: x + n

def loop(n, acc):
    while n != 0:
        f = compose(make_adder(1), make_adder(n))
        acc = f(acc)
        n -= 1
    return acc

print(loop(1000000, 0))
