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

      echo getAssertions()

  test "Contamination-free":
    z3:
      check 5 == 2 + 3


  test "Uninterpreted Functions":
    z3:
      let
        f = declFunc("f", params(RealSort), RealSort)
        x = declRealConst("x")

      assert distinc(x, 0.0, 1.0)
      assert f.apply(params(x)) == x + f.apply(params(0.0.toAst()))

      check check() == sat
      echo getModel()

  test "AST vector":
    z3:
      let
        x = declIntConst(1)
        y = declIntConst(2)
        z = declIntConst(3)

      assert x + y > z

      z3block:
        assert 3 * x + y < 2 * z

        check getAssertions().len == 2

        assert x > 0

        check getAssertions().len == 3

      check getAssertions().len == 1

  test "timeout":
    z3:
      # negation of Goldbach's conjecture (one of unsolved problems)
      let
        x = declConst(1, IntSort)
        y = declConst(2, IntSort)
        z = declConst(3, IntSort)
        wy = declConst(4, IntSort)
        wz = declConst(5, IntSort)

      assert x > 3
      assert x mod 2 == 0

      assert forall(params(y, z, wy, wz), (((1 < wy and wy < y) ==> (y mod wy != 0)) and ((1 < wz and wz < z) ==> (z mod wz != 0))) ==> (x != y + z))

      z3block:
        setTimeout(3_000'u)
        check check() == undefined

  test "recursive function":
    z3:
      let
        x = declConst("x", IntSort)
        a = declConst("a", IntSort)

        f = defRecursiveFunc("f", params(IntSort, IntSort), IntSort, params(x, a)):
          ite(x <= 0, a, recur.apply(params(x - 1, a * x)))

        n = declConst("n", IntSort)

      proc factorial(x: Ast[IntSort]): Ast[IntSort] =
        f.apply(params(x, toAst(1)))

      assert factorial(n) > 1000
      check check() == sat
