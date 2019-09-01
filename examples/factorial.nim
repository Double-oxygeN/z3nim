import z3nim

z3:
  let
    x = declConst(0, IntSort)
    a = declConst(1, IntSort)

    f = defRecursiveFunc("f", params(x, a), IntSort):
      ite(x <= 0, a, recur.apply(params(x - 1, a * x)))

    n = declConst(3, IntSort)

  proc factorial(x: Ast[IntSort]): Ast[IntSort] =
    f.apply(params(x, toAst(1)))

  assert factorial(n) > 1_000
  assert factorial(n) < 10_000

  echo check()
  echo getModel()
