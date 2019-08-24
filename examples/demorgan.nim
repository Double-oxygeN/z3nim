import ../src/z3nim

z3:
  let
    x = declBoolConst("x")
    y = declBoolConst("y")

  assert not ((not (x and y)) == (not x or not y))
  echo check
