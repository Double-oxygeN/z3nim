import ../src/z3nim

z3:
  let
    realSort = makeSort(RealSort)
    boolSort = makeSort(BoolSort)

    f = declFunc("f", singleton(realSort), boolSort)
    g = declFunc("g", pair(realSort, singleton(boolSort)), boolSort)
    x = declConst("x", realSort)

  assert not f.apply(singleton(x))
  assert g.apply(pair(x, singleton(toAst(false))))
  assert not g.apply(pair(x, singleton(toAst(true))))

  echo check()
  echo getModel()
