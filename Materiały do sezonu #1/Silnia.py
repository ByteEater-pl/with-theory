def factorial(n):
  return factorial(n - 1) * n if n > 1 else 1

def factorial2(n):
  fac = 1
  for i in range(2, n + 1):
    fac *= i
  return fac

print(factorial(43) - factorial2(43))
