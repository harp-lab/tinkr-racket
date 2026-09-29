def loop(n, acc):
    while n != 0:
        acc += n
        n -= 1
    return acc

print(loop(3000000, 0))
