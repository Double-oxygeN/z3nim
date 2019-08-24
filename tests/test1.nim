import unittest, strformat
import z3nim/z3api

suite "API":
  test "Version":
    var a, b, c, d: cuint
    Z3GetVersion(addr a, addr b, addr c, addr d)

    check Z3GetFullVersion() == fmt"Z3 {a}.{b}.{c}.{d}"

  test "Simple Example":
    let
      cfg = Z3MkConfig()
      ctx = Z3MkContext(cfg)

    Z3DelConfig(cfg)
    Z3DelContext(ctx)

  test "De Morgan":
    let
      cfg = Z3MkConfig()
      ctx = Z3MkContext(cfg)

    Z3DelConfig(cfg)

    let
      boolSort = ctx.Z3MkBoolSort()
      xSym = ctx.Z3MkStringSymbol("x")
      ySym = ctx.Z3MkStringSymbol("y")
      x = ctx.Z3MkConst(xSym, boolSort)
      y = ctx.Z3MkConst(ySym, boolSort)
      notX = ctx.Z3MkNot(x)
      notY = ctx.Z3MkNot(y)

    var args1 = [x, y]
    let xNandY = ctx.Z3MkNot(ctx.Z3MkAnd(2'u.cuint, cast[carray[Z3Ast]](addr args1[0])))

    var args2 = [notX, notY]
    let notXOrNotY = ctx.Z3MkOr(2'u.cuint, cast[carray[Z3Ast]](addr args2[0]))

    let negatedConjecture = ctx.Z3MkNot(ctx.Z3MkIff(xNandY, notXOrNotY))

    let solver = ctx.Z3MkSolver()

    ctx.Z3SolverIncRef(solver)
    ctx.Z3SolverAssert(solver, negatedConjecture)

    check ctx.Z3SolverCheck(solver) == Z3LFalse

    ctx.Z3SolverDecRef(solver)
    Z3DelContext(ctx)

  test "Linear Algebra":
    Z3GlobalParamSet("pp.decimal", "true")
    let
      cfg = Z3MkConfig()
      ctx = Z3MkContext(cfg)

    Z3DelConfig cfg

    let
      realSort = ctx.Z3MkRealSort()
      x = [
        ctx.Z3MkConst(ctx.Z3MkIntSymbol(1), realSort),
        ctx.Z3MkConst(ctx.Z3MkIntSymbol(2), realSort),
        ctx.Z3MkConst(ctx.Z3MkIntSymbol(3), realSort),
        ctx.Z3MkConst(ctx.Z3MkIntSymbol(4), realSort)
      ]

    template makeLinearExpression(coeffs: varargs[float]): Z3Ast =
      var monomials: array[coeffs.len, Z3Ast]

      for i, coeff in coeffs:
        var args = [ctx.Z3MkNumeral($coeff, realSort), x[i]]
        monomials[i] = ctx.Z3MkMul(2'u.cuint, cast[carray[Z3Ast]](addr args[0]))

      ctx.Z3MkAdd(coeffs.len.cuint, cast[carray[Z3Ast]](addr monomials[0]))

    let
      e1 = makeLinearExpression(272.95, 163.34, 469.51, -12.4)
      l1 = ctx.Z3MkEq(e1, ctx.Z3MkNumeral("204.7479", realSort))
      e2 = makeLinearExpression(-83.65, 289.16, -268.18, 23.43)
      l2 = ctx.Z3MkEq(e2, ctx.Z3MkNumeral("165.33", realSort))
      e3 = makeLinearExpression(506.71, -886.23, 740.67, -290.88)
      l3 = ctx.Z3MkEq(e3, ctx.Z3MkNumeral("466.2096", realSort))
      e4 = makeLinearExpression(108.32, 330.63, 97.02, 13.35)
      l4 = ctx.Z3MkEq(e4, ctx.Z3MkNumeral("222.7266", realSort))

      solver = ctx.Z3MkSolver()

    ctx.Z3SolverIncRef(solver)

    ctx.Z3SolverAssert(solver, l1)
    ctx.Z3SolverAssert(solver, l2)
    ctx.Z3SolverAssert(solver, l3)
    ctx.Z3SolverAssert(solver, l4)

    check ctx.Z3SolverCheck(solver) == Z3LTrue

    echo ctx.Z3ModelToString(ctx.Z3SolverGetModel(solver))

    ctx.Z3SolverDecRef(solver)
    Z3DelContext ctx
