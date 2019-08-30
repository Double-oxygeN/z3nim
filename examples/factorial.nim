import z3nim

z3:
  let
    x = declConst(0, IntSort)
    a = declConst(1, IntSort)

    f = defRecursiveFunc("f", params(IntSort, IntSort), IntSort, params(x, a)):
      ite(x <= 0, a, recur.apply(params(x - 1, a * x)))

    n = declConst(3, IntSort)

  proc factorial(x: Ast[IntSort]): Ast[IntSort] =
    f.apply(params(x, toAst(1)))

  assert factorial(n) > 1000

  echo check()
  echo getModel()