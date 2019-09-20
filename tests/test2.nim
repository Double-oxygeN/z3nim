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

      let model = getModel()

      echo model.eval(x1).toFloat()
      echo model.eval(x2).toFloat()
      echo model.eval(x3).toFloat()
      echo model.eval(x4).toFloat()

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

  test "floating-point number":
    z3:
      const
        sumXY = 0b0_10000001_10111000_00000000_0000000'f32
        diffXY = 0b0_10000000_10110000_00000000_0000000'f32
      let
        x = declConst("x", Float32Sort)
        y = declConst("y", Float32Sort)
        z = declConst("z", Float64Sort)

      assert x + y == toFloat32Ast(sumXY)
      assert x - y == toFloat32Ast(diffXY)
      assert z.isNaN()

      check check() == sat
      let model = getModel()

      echo "x -> ", model.eval(x)
      echo "y -> ", model.eval(y)
      check model.eval((x + y).toReal()).toFloat() == sumXY
      check model.eval((x - y).toReal()).toFloat() == diffXY

      echo "z -> ", model.eval(z)

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
        setTimeout(1_000'u)
        check check() == undefined
        check getReason() in ["canceled", "timeout"]

  test "recursive function":
    z3:
      let
        x = declConst("x", IntSort)
        a = declConst("a", IntSort)

        f = defRecursiveFunc("f", params(x, a), IntSort):
          ite(x <= 0, a, recur.apply(params(x - 1, a * x)))

        n = declConst("n", IntSort)

      proc factorial(x: Ast[IntSort]): Ast[IntSort] =
        f.apply(params(x, toAst(1)))

      assert factorial(n) > 1000
      assert factorial(n) < 10000
      check check() == sat

  test "evaluation":
    z3:
      let
        x = declConst("x", RealSort)
        y = declConst("y", RealSort)
        z = declConst("z", RealSort)

      assert x + y + z == 6.0
      assert x + y < 4.5
      assert x + z > 2.5
      assert y > z + 0.8

      check check() == sat

      let
        model = getModel()

        xVal = model.eval(x).toFloat()
        yVal = model.eval(y).toFloat()
        zVal = model.eval(z).toFloat()

      assert xVal + yVal + zVal == 6.0
      assert xVal + yVal < 4.5
      assert xVal + zVal > 2.5
      assert yVal > zVal + 0.8

  test "array1":
    z3:
      var
        arr1 = declConst(1, ArraySort[IntSort, IntSort])

      arr1[3] = toAst(42)
      arr1[4] = toAst(53)

      for i in 0..2:
        assert arr1[i + 1] - arr1[i] == arr1[i + 2] - arr1[i + 1]

      check check() == sat

      let model = getModel()

      check model.eval(arr1[0]).toInt() == 9

  test "array2":
    z3:
      let
        b1 = declBoolConst("b1")
        r1 = declRealConst("r1")
      var
        arr2 = declConst(2, ArraySort[BoolSort, RealSort])

      arr2[b1] = r1

      assert r1 > 0'f
      assert arr2[not b1] == -arr2[b1]

      check check() == sat

      let model = getModel()
      
      check model.eval(arr2[not b1]).toFloat() == -model.eval(r1).toFloat()
