import z3nim

z3:
  let
    f = declFunc("f", params(RealSort), BoolSort)
    g = declFunc("g", params(RealSort, BoolSort), BoolSort)
    x = declConst("x", RealSort)

  assert not f.apply(params(x))
  assert g.apply(params(x, toAst(false)))
  assert not g.apply(params(x, toAst(true)))

  echo check()
  echo getModel()
