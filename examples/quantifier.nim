import ../src/z3nim

z3:
  let
    x = declIntConst("x")
    y = declIntConst("y")
    z = declIntConst("z")

    f = declFunc("f", params(IntSort, IntSort), IntSort)

  echo forall(params(x, y, z), (f.apply(params(x, y)) == z) ==> distinc(x, z) and distinc(y, z))
  echo exists(params(x, y, z), (f.apply(params(x, y)) == z) ==> distinc(x, z) and distinc(y, z))
