import ../src/z3nim

z3:
  let
    x = declIntConst("x")
    y = declIntConst("y")
    z = declIntConst("z")

    f = declFunc("f", pair(IntSort, singleton(IntSort)), IntSort)

  echo forall(pair(x, pair(y, singleton(z))), (f.apply(pair(x, singleton(y))) == z) ==> distinc(x, z) and distinc(y, z))
  echo exists(pair(x, pair(y, singleton(z))), (f.apply(pair(x, singleton(y))) == z) ==> distinc(x, z) and distinc(y, z))
