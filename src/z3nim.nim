# Copyright (c) 2019 Double-oxygeN
# 
# This software is released under the MIT License.
# https://opensource.org/licenses/MIT

## :Author: `Double-oxygeN <https://github.com/Double-oxygeN>`_
## :License: MIT
##
## Z3 Nim binding.

import z3nim/z3api
import hashes, ropes
import macros except params

type
  Version* = object
    major, minor, build, revision: uint

  CheckResult* = enum
    unsat = -1, undefined, sat

  BoolSort* = object
  IntSort* = object
  RealSort* = object
  BitVecSort*[N: static uint] = object
  ArraySort*[D, R] = object
  SetSort*[T] = object
  UnknownSort* = object

  NumericSort* = IntSort | RealSort

  Pair[T1, T2] = object

  Sort*[T] = distinct Z3Sort
  Ast*[T] = distinct Z3Ast
  Model* = distinct Z3Model

  Sorts*[T] = distinct seq[Z3Sort]
  Asts*[T] = distinct seq[Z3Ast]

  FuncDecl*[D, R] = distinct Z3FuncDecl

  AstVector* = distinct Z3AstVector


func major*(self: Version): uint = self.major
func minor*(self: Version): uint = self.minor
func build*(self: Version): uint = self.build
func revision*(self: Version): uint = self.revision
func `$`*(self: Version): string =
  $self.major & '.' & $self.minor & '.' & $self.build & '.' & $self.revision


proc getZ3Version*: Version {.inline.} =
  ## Get current Z3 version.
  runnableExamples:
    echo "Z3 ", getZ3Version()

  Z3GetVersion(
    cast[ptr cuint](addr result.major),
    cast[ptr cuint](addr result.minor),
    cast[ptr cuint](addr result.build),
    cast[ptr cuint](addr result.revision)
  )


template z3*(body: untyped): untyped =
  ## Z3 environment block.
  runnableExamples:
    z3:
      let
        x = declBoolConst("x")
        y = declBoolConst("y")

      assert not ((not (x and y)) == (not x or not y))
      assert check() == unsat

  block:
    let cfg = Z3MkConfig()

    Z3SetParamValue(cfg, "proof", "true")
    Z3SetParamValue(cfg, "timeout", $60_000)
    Z3SetParamValue(cfg, "well_sorted_check", "true")
    Z3SetParamValue(cfg, "model", "true")
    Z3SetParamValue(cfg, "unsat_core", "true")

    let ctx {.inject, used.} = Z3MkContext(cfg)

    Z3DelConfig(cfg)

    let solver {.inject, used.} = Z3MkSolver(ctx)

    Z3SolverIncRef(ctx, solver)

    block:
      body

    Z3SolverDecRef(ctx, solver)
    Z3DelContext(ctx)


template z3block*(body: untyped): untyped =
  ## Z3 inner block.
  ##
  ## This is almost the same as the C code below.
  ##
  ## .. code-block::c
  ##   Z3_solver_push(ctx, solver);
  ##   /* body */
  ##   Z3_solver_pop(ctx, solver, 1);

  Z3_solver_push(ctx, solver)

  block:
    body

  Z3_solver_pop(ctx, solver, 1'u.cuint)

proc mkSort(ctx: Z3Context; s: typedesc[BoolSort]): Z3Sort = ctx.Z3MkBoolSort()
proc mkSort(ctx: Z3Context; s: typedesc[IntSort]): Z3Sort = ctx.Z3MkIntSort()
proc mkSort(ctx: Z3Context; s: typedesc[RealSort]): Z3Sort = ctx.Z3MkRealSort()
proc mkSort[N: static uint](ctx: Z3Context; s: typedesc[BitVecSort[N]]): Z3Sort = ctx.Z3MkBvSort(N.cuint)
proc mkSort[D, R](ctx: Z3Context; s: typedesc[ArraySort[D, R]]): Z3Sort = ctx.Z3MkArraySort(mkSort(ctx, D), mkSort(ctx, R))
proc mkSort[T](ctx: Z3Context; s: typedesc[SetSort[T]]): Z3Sort = ctx.Z3MkSetSort(mkSort(ctx, T))


template makeSort*(S: typedesc): Sort[S] =
  ## Make a sort.
  mixin mkSort
  Sort[S](mkSort(ctx, S))


template singleton[S](s: Sort[S]): Sorts[S] =
  Sorts[S](@[Z3Sort(s)])

template pair[S1, S2](s1: Sort[S1]; s2: Sorts[S2]): Sorts[Pair[S1, S2]] =
  Sorts[Pair[S1, S2]](Z3Sort(s1) & seq[Z3Sort](s2))


template singleton(S: typedesc): Sorts[S] =
  mixin mkSort
  Sorts[S](@[mkSort(ctx, S)])

template pair[S2](S1: typedesc; s2: Sorts[S2]): Sorts[Pair[S1, S2]] =
  mixin mkSort
  Sorts[Pair[S1, S2]](mkSort(ctx, S1) & seq[Z3Sort](s2))


template singleton[S](a: Ast[S]): Asts[S] =
  Asts[S](@[Z3Ast(a)])

template pair[S1, S2](a1: Ast[S1]; a2: Asts[S2]): Asts[Pair[S1, S2]] =
  Asts[Pair[S1, S2]](Z3Ast(a1) & seq[Z3Ast](a2))


macro params*(args: varargs[untyped]): untyped =
  ## Construct parameters.
  ##
  ## If each argument is either a type descriptor or a sort, then it becomes ``Sorts``.
  ## If each argument is an AST, then it becomes ``Asts``.
  runnableExamples:
    z3:
      let
        f1 = declFunc(1, params(IntSort), IntSort)
        f2 = declFunc(2, params(BoolSort, IntSort), BoolSort)

        x = declConst("x", IntSort)

      assert forall(params(x), f1.apply(params(x)) > toAst(0))
      assert exists(params(x), f2.apply(params(toAst(true), x)))

      assert check() == sat

  let lastArg = args[^1]
  result = quote do:
    singleton(`lastArg`)

  for i in 2..args.len:
    let arg = args[^i]
    result = quote do:
      pair(`arg`, `result`)


template declConst[S](sym: Z3Symbol; s: Sort[S]): Ast[S] =
  Ast[S](Z3MkConst(ctx, sym, Z3Sort(s)))

template declConst*(id: string; S: typedesc): Ast[S] =
  ## Declare a constant.
  let sym = Z3MkStringSymbol(ctx, id)
  declConst(sym, makeSort(S))

template declConst*(id: int; S: typedesc): Ast[S] =
  ## Declare a constant.
  let sym = Z3MkIntSymbol(ctx, id.cint)
  declConst(sym, makeSort(S))


template declBoolConst*(id: string | int): Ast[BoolSort] =
  ## Shorthand for ``declConst(id, BoolSort)``.
  declConst(id, BoolSort)

template declIntConst*(id: string | int): Ast[IntSort] =
  ## Shorthand for ``declConst(id, IntSort)``.
  declConst(id, IntSort)

template declRealConst*(id: string | int): Ast[RealSort] =
  ## Shorthand for ``declConst(id, RealSort)``.
  declConst(id, RealSort)

template declBitVecConst*(id: string | int; size: static uint): Ast[BitVecSort[size]] =
  ## Shorthand for ``declConst(id, BitVecSort[size])``.
  declConst(id, BitVecSort[size])


template declFunc[D](sym: Z3Symbol; domains: Sorts[D]; R: typedesc): FuncDecl[D, R] =
  let
    domainsSeq = seq[Z3Sort](domains)
  var
    domainsPtr = alloc(domainsSeq.len * sizeof(Z3Sort))
    domainsArr = cast[carray[Z3Sort]](domainsPtr)

  for idx, dom in domainsSeq:
    domainsArr[idx] = dom

  let fn = FuncDecl[D, R](Z3MkFuncDecl(ctx, sym, domainsSeq.len.cuint, domainsArr, mkSort(ctx, R)))

  dealloc domainsPtr

  fn

template declFunc*[D](id: string; domains: Sorts[D]; R: typedesc): FuncDecl[D, R] =
  ## Declare a function.
  runnableExamples:
    z3:
      let
        f = declFunc("f", params(RealSort, RealSort), RealSort)
        x = declRealConst("x")

      assert f.apply(params(x, x)) == x
      assert check() == sat

  let sym = Z3MkStringSymbol(ctx, id)
  declFunc(sym, domains, R)

template declFunc*[D](id: int; domains: Sorts[D]; R: typedesc): FuncDecl[D, R] =
  ## Declare a function.
  runnableExamples:
    z3:
      let
        f = declFunc(0, params(RealSort, RealSort), RealSort)
        x = declRealConst(1)

      assert f.apply(params(x, x)) == x
      assert check() == sat

  let sym = Z3MkIntSymbol(ctx, id.cint)
  declFunc(sym, domains, R)


template toAst*[S](a: Ast[S]): Ast[S] =
  ## Convert to Z3 AST.
  ## This is an identity function.
  a

template toAst*(b: bool): Ast[BoolSort] =
  ## Convert from a boolean value to Z3 AST.
  if b: Ast[BoolSort](Z3MkTrue(ctx)) else: Ast[BoolSort](Z3MkFalse(ctx))

template toAst*(i: int): Ast[IntSort] =
  ## Convert from an integer value to Z3 AST.
  Ast[IntSort](Z3MkInt(ctx, i.cint, Z3MkIntSort(ctx)))

template toAst*(r: float): Ast[RealSort] =
  ## Convert from a float value to Z3 AST.
  Ast[RealSort](Z3MkNumeral(ctx, $r, Z3MkRealSort(ctx)))


template `not`*(arg: Ast[BoolSort]): Ast[BoolSort] =
  Ast[BoolSort](Z3MkNot(ctx, Z3Ast(arg)))

template boolAnd*(args: varargs[Ast[BoolSort], toAst]): Ast[BoolSort] =
  var
    argsPtr = alloc(len(args) * sizeof(Z3Ast))
    argsArr = cast[carray[Z3Ast]](argsPtr)

  for idx, arg in args:
    argsArr[idx] = Z3Ast(arg)

  let a = Ast[BoolSort](Z3MkAnd(ctx, cuint(len(args)), argsArr))

  dealloc argsPtr

  a

template `and`*(arg1, arg2: untyped): untyped =
  boolAnd(arg1, arg2)

template boolOr*(args: varargs[Ast[BoolSort], toAst]): Ast[BoolSort] =
  var
    argsPtr = alloc(len(args) * sizeof(Z3Ast))
    argsArr = cast[carray[Z3Ast]](argsPtr)

  for idx, arg in args:
    argsArr[idx] = Z3Ast(arg)

  let a = Ast[BoolSort](Z3MkOr(ctx, cuint(len(args)), argsArr))

  dealloc argsPtr

  a

template `or`*(arg1, arg2: untyped): untyped =
  boolOr(arg1, arg2)

template `xor`*(arg1, arg2: Ast[BoolSort]): Ast[BoolSort] =
  Ast[BoolSort](Z3MkXor(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `xor`*(arg1: bool; arg2: Ast[BoolSort]): Ast[BoolSort] =
  if arg1: not arg2 else: arg2

template `xor`*(arg1: Ast[BoolSort]; arg2: bool): Ast[BoolSort] = arg2 xor arg1

template `==`*[S](arg1, arg2: Ast[S]): Ast[BoolSort] =
  when S is BoolSort:
    Ast[BoolSort](Z3MkIff(ctx, Z3Ast(arg1), Z3Ast(arg2)))
  else:
    Ast[BoolSort](Z3MkEq(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `==`*(arg1: bool; arg2: Ast[BoolSort]): Ast[BoolSort] =
  toAst(arg1) == arg2

template `==`*(arg1: Ast[BoolSort]; arg2: bool): Ast[BoolSort] =
  arg1 == toAst(arg2)

template `==`*(arg1: int; arg2: Ast[IntSort]): Ast[BoolSort] =
  toAst(arg1) == arg2

template `==`*(arg1: Ast[IntSort]; arg2: int): Ast[BoolSort] =
  arg1 == toAst(arg2)

template `==`*(arg1: float; arg2: Ast[RealSort]): Ast[BoolSort] =
  toAst(arg1) == arg2

template `==`*(arg1: Ast[RealSort]; arg2: float): Ast[BoolSort] =
  arg1 == toAst(arg2)

template distinc*[S](args: varargs[Ast[S], toAst]): Ast[BoolSort] =
  var
    argsPtr = alloc(len(args) * sizeof(Z3Ast))
    argsArr = cast[carray[Z3Ast]](argsPtr)

  for idx, arg in args:
    argsArr[idx] = Z3Ast(arg)

  let a = Ast[BoolSort](Z3MkDistinct(ctx, cuint(len(args)), argsArr))

  dealloc argsPtr

  a

template `==>`*(arg1, arg2: Ast[BoolSort]): Ast[BoolSort] =
  Ast[BoolSort](Z3MkImplies(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `==>`*(arg1: bool; arg2: Ast[BoolSort]): Ast[BoolSort] =
  if arg1: arg2 else: Ast[BoolSort](Z3MkTrue(ctx))

template `==>`*(arg1: Ast[BoolSort]; arg2: bool): Ast[BoolSort] =
  if arg2: Ast[BoolSort](Z3MkTrue(ctx)) else: Ast[BoolSort](Z3MkNot(ctx, Z3Ast(arg1)))

template astAdd*[S: NumericSort](args: varargs[Ast[S], toAst]): Ast[S] =
  var
    argsPtr = alloc(len(args) * sizeof(Z3Ast))
    argsArr = cast[carray[Z3Ast]](argsPtr)

  for idx, arg in args:
    argsArr[idx] = Z3Ast(arg)

  let a = Ast[S](Z3MkAdd(ctx, cuint(len(args)), argsArr))

  dealloc argsPtr

  a

template `+`*(arg1, arg2: untyped): untyped =
  astAdd(arg1, arg2)

template astMul*[S: NumericSort](args: varargs[Ast[S], toAst]): Ast[S] =
  var
    argsPtr = alloc(len(args) * sizeof(Z3Ast))
    argsArr = cast[carray[Z3Ast]](argsPtr)

  for idx, arg in args:
    argsArr[idx] = Z3Ast(arg)

  let a = Ast[S](Z3MkMul(ctx, cuint(len(args)), argsArr))

  dealloc argsPtr

  a

template `*`*(arg1, arg2: untyped): untyped =
  astMul(arg1, arg2)

template `-`*[S: NumericSort](arg: Ast[S]): Ast[S] =
  Ast[S](Z3MkUnaryMinus(ctx, Z3Ast(arg)))

template astSub*[S: NumericSort](args: varargs[Ast[S], toAst]): Ast[S] =
  var
    argsPtr = alloc(len(args) * sizeof(Z3Ast))
    argsArr = cast[carray[Z3Ast]](argsPtr)

  for idx, arg in args:
    argsArr[idx] = Z3Ast(arg)

  let a = Ast[S](Z3MkSub(ctx, cuint(len(args)), argsArr))

  dealloc argsPtr

  a

template `-`*(arg1, arg2: untyped): untyped =
  astSub(arg1, arg2)

template `div`*(arg1, arg2: Ast[IntSort]): Ast[IntSort] =
  Ast[IntSort](Z3MkDiv(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `div`*(arg1: int; arg2: Ast[IntSort]): Ast[IntSort] =
  toAst(arg1) div arg2

template `div`*(arg1: Ast[IntSort]; arg2: int): Ast[IntSort] =
  arg1 div toAst(arg2)

template `/`*(arg1, arg2: Ast[RealSort]): Ast[RealSort] =
  Ast[RealSort](Z3MkDiv(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `/`*(arg1: float; arg2: Ast[RealSort]): Ast[RealSort] =
  toAst(arg1) / arg2

template `/`*(arg1: Ast[RealSort]; arg2: float): Ast[RealSort] =
  arg1 / toAst(arg2)

template `mod`*(arg1, arg2: Ast[IntSort]): Ast[IntSort] =
  Ast[IntSort](Z3MkMod(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `mod`*(arg1: int; arg2: Ast[IntSort]): Ast[IntSort] =
  toAst(arg1) mod arg2

template `mod`*(arg1: Ast[IntSort]; arg2: int): Ast[IntSort] =
  arg1 mod toAst(arg2)

template `^`*[S: NumericSort](arg1, arg2: Ast[S]): Ast[S] =
  Ast[S](Z3MkPower(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `^`*(arg1: int; arg2: Ast[IntSort]): Ast[IntSort] =
  toAst(arg1) ^ arg2

template `^`*(arg1: Ast[IntSort]; arg2: int): Ast[IntSort] =
  case arg2
  of 0: toAst(1)
  of 1: arg1
  of 2: arg1 * arg1
  else: arg1 ^ toAst(arg2)

template `^`*(arg1: float; arg2: Ast[RealSort]): Ast[RealSort] =
  toAst(arg1) ^ arg2

template `^`*(arg1: Ast[RealSort]; arg2: float): Ast[RealSort] =
  arg1 ^ toAst(arg2)

template `<`*[S: NumericSort](arg1, arg2: Ast[S]): Ast[BoolSort] =
  Ast[BoolSort](Z3MkLt(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `<`*(arg1: int; arg2: Ast[IntSort]): Ast[BoolSort] =
  toAst(arg1) < arg2

template `<`*(arg1: Ast[IntSort]; arg2: int): Ast[BoolSort] =
  arg1 < toAst(arg2)

template `<`*(arg1: float; arg2: Ast[RealSort]): Ast[BoolSort] =
  toAst(arg1) < arg2

template `<`*(arg1: Ast[RealSort]; arg2: float): Ast[BoolSort] =
  arg1 < toAst(arg2)

template `<=`*[S: NumericSort](arg1, arg2: Ast[S]): Ast[BoolSort] =
  Ast[BoolSort](Z3MkLe(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `<=`*(arg1: int; arg2: Ast[IntSort]): Ast[BoolSort] =
  toAst(arg1) <= arg2

template `<=`*(arg1: Ast[IntSort]; arg2: int): Ast[BoolSort] =
  arg1 <= toAst(arg2)

template `<=`*(arg1: float; arg2: Ast[RealSort]): Ast[BoolSort] =
  toAst(arg1) <= arg2

template `<=`*(arg1: Ast[RealSort]; arg2: float): Ast[BoolSort] =
  arg1 <= toAst(arg2)

template `>`*[S: NumericSort](arg1, arg2: Ast[S]): Ast[BoolSort] =
  Ast[BoolSort](Z3MkGt(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `>`*(arg1: int; arg2: Ast[IntSort]): Ast[BoolSort] =
  toAst(arg1) > arg2

template `>`*(arg1: Ast[IntSort]; arg2: int): Ast[BoolSort] =
  arg1 > toAst(arg2)

template `>`*(arg1: float; arg2: Ast[RealSort]): Ast[BoolSort] =
  toAst(arg1) > arg2

template `>`*(arg1: Ast[RealSort]; arg2: float): Ast[BoolSort] =
  arg1 > toAst(arg2)

template `>=`*[S: NumericSort](arg1, arg2: Ast[S]): Ast[BoolSort] =
  Ast[BoolSort](Z3MkGe(ctx, Z3Ast(arg1), Z3Ast(arg2)))

template `>=`*(arg1: int; arg2: Ast[IntSort]): Ast[BoolSort] =
  toAst(arg1) >= arg2

template `>=`*(arg1: Ast[IntSort]; arg2: int): Ast[BoolSort] =
  arg1 >= toAst(arg2)

template `>=`*(arg1: float; arg2: Ast[RealSort]): Ast[BoolSort] =
  toAst(arg1) >= arg2

template `>=`*(arg1: Ast[RealSort]; arg2: float): Ast[BoolSort] =
  arg1 >= toAst(arg2)

template int2real*(arg: Ast[IntSort]): Ast[RealSort] =
  Ast[RealSort](Z3MkInt2Real(ctx, Z3Ast(arg)))

template real2int*(arg: Ast[RealSort]): Ast[IntSort] =
  Ast[IntSort](Z3MkReal2Int(ctx, Z3Ast(arg)))

template isInt*(arg: Ast[RealSort]): Ast[BoolSort] =
  Ast[BoolSort](Z3MkIsInt(ctx, Z3Ast(arg)))

template apply*[D, R](fn: FuncDecl[D, R]; args: Asts[D]): Ast[R] =
  let argsSeq = seq[Z3Ast](args)
  var
    argsPtr = alloc(argsSeq.len * sizeof(Z3Ast))
    argsArr = cast[carray[Z3Ast]](argsPtr)

  for idx, arg in argsSeq:
    argsArr[idx] = arg

  let a = Ast[R](Z3MkApp(ctx, Z3FuncDecl(fn), argsSeq.len.cuint, argsArr))

  dealloc argsPtr

  a

template quantifier[V, S](isForall: bool; apps: Asts[V]; body: Ast[S]): Ast[S] =
  let appsSeq = seq[Z3Ast](apps)
  var
    boundPtr = alloc(appsSeq.len * sizeof(Z3App))
    boundArr = cast[ptr UncheckedArray[Z3App]](boundPtr)

  for idx, app in appsSeq:
    assert(Z3IsApp(ctx, app), "Unsupported `apps` is given. It only supports either constants or applications (Z3_APP_AST).")
    boundArr[idx] = Z3ToApp(ctx, app)

  let a = Ast[S](Z3MkQuantifierConst(ctx, isForall, 0'u.cuint, appsSeq.len.cuint, boundArr, 0'u.cuint, nil, Z3Ast(body)))

  dealloc boundPtr

  a

template forall*[V, S](apps: Asts[V]; body: Ast[S]): Ast[S] =
  quantifier(true, apps, body)

template exists*[V, S](apps: Asts[V]; body: Ast[S]): Ast[S] =
  quantifier(false, apps, body)

template assert*(t: Ast[BoolSort]) =
  Z3SolverAssert(ctx, solver, Z3Ast(t))

template check*: CheckResult =
  Z3SolverCheck(ctx, solver).ord.CheckResult

template getModel*: Model =
  Model(Z3SolverGetModel(ctx, solver))

template getAssertions*: AstVector =
  AstVector(Z3SolverGetAssertions(ctx, solver))

template getProof*: Ast[UnknownSort] =
  Ast[UnknownSort](Z3SolverGetProof(ctx, solver))


template `$`*[S](sort: Sort[S]): string =
  $Z3SortToString(ctx, Z3Sort(sort))

template `$`*[S](sorts: Sorts[S]): string =
  var r = rope("(")
  let sortsSeq = seq[Z3Sort](sorts)

  r.add($Z3SortToString(ctx, sortsSeq[0]))

  if len(sortsSeq) > 1:
    for sort in sortsSeq[1..^1]:
      r.add(", ")
      r.add($Z3SortToString(ctx, sort))

  r.add(")")
  $r

template `$`*[S](ast: Ast[S]): string =
  $Z3AstToString(ctx, Z3Ast(ast))

template `$`*[S](asts: Asts[S]): string =
  var r = rope("(")
  let astsSeq = seq[Z3Ast](asts)

  add(r, $Z3AstToString(ctx, astsSeq[0]))

  if len(astsSeq) > 1:
    for ast in astsSeq[1..^1]:
      add(r, ", ")
      add(r, $Z3AstToString(ctx, ast))

  add(r, ")")
  $r

template `$`*(model: Model): string =
  $Z3ModelToString(ctx, Z3Model(model))

template `$`*[D, R](fn: FuncDecl[D, R]): string =
  $Z3FuncDeclToString(ctx, Z3FuncDecl(fn))

template `$`*(astvec: AstVector): string =
  $Z3AstVectorToString(ctx, Z3AstVector(astvec))

template len*(astvec: AstVector): int =
  int(Z3AstVectorSize(ctx, Z3AstVector(astvec)))

template `===`*[S](t1, t2: Ast[S]): bool =
  Z3IsEqAst(ctx, Z3Ast(t1), Z3Ast(t2))

template `==`*[S](s1, s2: Sort[S]): bool =
  Z3IsEqSort(ctx, Z3Sort(s1), Z3Sort(s2))

template `==`*[D,R](f1, f2: FuncDecl[D, R]): bool =
  Z3IsEqFuncDecl(ctx, Z3FuncDecl(f1), Z3FuncDecl(f2))

template hash*[S](a: Ast[S]): Hash =
  var h: Hash = 0
  h = h !& hash(Z3GetAstHash(ctx, a))
  !$h
