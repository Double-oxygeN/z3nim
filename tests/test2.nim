import unittest
import z3nim

from z3nim/z3api import Z3GetFullVersion

suite "Library":
  test "Version":
    let version = getZ3Version()
    check "Z3 " & $version == Z3GetFullVersion()

  test "De Morgan's law":
    z3:
      let
        x = declConst("x", BoolSort)
        y = declBoolConst("y")

      assert not ((not (x and y)) == (not x or not y))
      check check() == unsat

  test "Linear Algebra":
    z3:
      let
        x1 = declRealConst(1)
        x2 = declRealConst(2)
        x3 = declRealConst(3)
        x4 = declRealConst(4)

      assert 272.95 * x1 + 163.34 * x2 + 469.51 * x3 - 12.4 * x4 == 204.7479
      assert -83.65 * x1 + 289.16 * x2 - 268.18 * x3 + 23.43 * x4 == 165.33
      assert 506.71 * x1 - 886.23 * x2 + 740.67 * x3 - 290.88 * x4 == 466.2096
      assert 108.32 * x1 + 330.63 * x2 + 97.02 * x3 + 13.35 * x4 == 222.7266

      check check() == sat

      echo getModel()

  test "Contamination-free":
    z3:
      assert 5 == 2 + 3


  test "Uninterpreted Functions":
    z3:
      let
        f = declFunc("f", singleton(RealSort), RealSort)
        x = declRealConst("x")

      assert distinc(x, 0.0, 1.0)
      assert f.apply(singleton(x)) == x + f.apply(singleton(0.0.toAst()))

      assert check() == sat
      echo getModel()
