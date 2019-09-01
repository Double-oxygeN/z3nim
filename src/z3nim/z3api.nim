## Z3 API for C
##
## For more information, visit http://z3prover.github.io/api/html/group__capi.html

import macros

const
  libZ3Name =
    when defined(windows): "libz3.dll"
    elif defined(macosx): "libz3.dylib"
    else: "libz3.so"

{.pragma: libz3, importc, dynlib: libZ3Name, cdecl.}

# Types
# =====

macro opaquePointers(typeNames: varargs[untyped]): untyped =
  var typeSection = nnkTypeSection.newTree()

  for typeName in typeNames:
    typeSection.add(nnkTypeDef.newTree(
      nnkPostfix.newTree(ident"*", typeName),
      newEmptyNode(),
      nnkDistinctTy.newTree(ident"pointer")
    ))

  result = newStmtList(typeSection)

opaquePointers(
  Z3_config,
  Z3_context,
  Z3_symbol,
  Z3_ast,
  Z3_sort,
  Z3_func_decl,
  Z3_app,
  Z3_pattern,
  Z3_constructor,
  Z3_constructor_list,
  Z3_params,
  Z3_param_descrs,
  Z3_model,
  Z3_func_interp,
  Z3_func_entry,
  Z3_fixedpoint,
  Z3_optimize,
  Z3_ast_vector,
  Z3_ast_map,
  Z3_goal,
  Z3_tactic,
  Z3_probe,
  Z3_apply_result,
  Z3_solver,
  Z3_stats
)

type
  Z3_sort_opt* = Z3_sort

  Z3_lbool* = enum
    Z3_L_FALSE = -1
    Z3_L_UNDEF
    Z3_L_TRUE

  Z3_symbol_kind* = enum
    Z3_INT_SYMBOL
    Z3_STRING_SYMBOL

  Z3_parameter_kind* = enum
    Z3_PARAMETER_INT
    Z3_PARAMETER_DOUBLE
    Z3_PARAMETER_RATIONAL
    Z3_PARAMETER_SORT
    Z3_PATAMETER_AST
    Z3_PARAMETER_FUNC_DECL

  Z3_sort_kind* = enum
    Z3_UNINTERPRETED_SORT
    Z3_BOOL_SORT
    Z3_INT_SORT
    Z3_REAL_SORT
    Z3_BV_SORT
    Z3_ARRAY_SORT
    Z3_DATATYPE_SORT
    Z3_RELATION_SORT
    Z3_FINITE_DOMAIN_SORT
    Z3_FLOATING_POINT_SORT
    Z3_ROUNDING_MODE_SORT
    Z3_SEQ_SORT
    Z3_RE_SORT
    Z3_UNKNOWN_SORT = 1_000

  Z3_ast_kind* = enum
    Z3_NUMERAL_AST
    Z3_APP_AST
    Z3_VAR_AST
    Z3_QUANTIFIER_AST
    Z3_SORT_AST
    Z3_FUNC_DECL_AST
    Z3_UNKNOWN_AST = 1_000

  Z3_param_kind* = enum
    Z3_PK_UINT
    Z3_PK_BOOL
    Z3_PK_DOUBLE
    Z3_PK_SYMBOL
    Z3_PK_STRING
    Z3_PK_OTHER
    Z3_PK_INVALID

  Z3_ast_print_mode* = enum
    Z3_PRINT_SMTLIB_FULL
    Z3_PRINT_LOW_LEVEL
    Z3_PRINT_SMTLIB_COMPLIANT

  Z3_error_code* = enum
    Z3_OK
    Z3_SORT_ERROR
    Z3_IOB
    Z3_INVALID_ARG
    Z3_PARSER_ERROR
    Z3_NO_PARSER
    Z3_INVALID_PATTERN
    Z3_MEMOUT_FAIL
    Z3_FILE_ACCESS_ERROR
    Z3_INTERNAL_FATAL
    Z3_INVALID_USAGE
    Z3_DEC_REF_ERROR
    Z3_EXCEPTION

  Z3_goal_prec* = enum
    Z3_GOAL_PRECISE
    Z3_GOAL_UNDER
    Z3_GOAL_OVER
    Z3_GOAL_UNDER_OVER

  Z3_bool* = bool
  Z3_string* = cstring
  Z3_string_ptr* = ptr Z3_string
  Z3_error_handler* = (proc (c: Z3_Context; e: Z3_error_code) {.nimcall.})

  carray*[T] = ptr UncheckedArray[T]

# Global Parameters
# =================

proc Z3_global_param_set*(param_id, param_value: Z3_string) {.libz3.}
proc Z3_global_param_reset* {.libz3.}
proc Z3_global_param_get*(param_id: Z3_string; param_value: Z3_string_ptr): Z3_bool {.libz3.}

# Create configuration
# ====================

proc Z3_mk_config*: Z3_config {.libz3.}
proc Z3_del_config*(c: Z3_config) {.libz3.}
proc Z3_set_param_value*(c: Z3_config; param_id, param_value: Z3_string) {.libz3.}

# Context and AST Reference Counting
# ==================================

proc Z3_mk_context*(c: Z3_config): Z3_context {.libz3.}
proc Z3_mk_context_rc*(c: Z3_config): Z3_context {.libz3.}
proc Z3_del_context*(c: Z3_context) {.libz3.}
proc Z3_inc_ref*(c: Z3_context; a: Z3_ast) {.libz3.}
proc Z3_dec_ref*(c: Z3_context; a: Z3_ast) {.libz3.}
proc Z3_update_param_value*(c: Z3_context; param_id, param_value: Z3_string) {.libz3.}
proc Z3_interrupt*(c: Z3_context) {.libz3.}

# Parameters
# ==========

proc Z3_mk_params*(c: Z3_context): Z3_params {.libz3.}
proc Z3_params_inc_ref*(c: Z3_context; p: Z3_params) {.libz3.}
proc Z3_params_dec_ref*(c: Z3_context; p: Z3_params) {.libz3.}
proc Z3_params_set_bool*(c: Z3_context; p: Z3_params; k: Z3_symbol; v: bool) {.libz3.}
proc Z3_params_set_uint*(c: Z3_context; p: Z3_params; k: Z3_symbol; v: cuint) {.libz3.}
proc Z3_params_set_double*(c: Z3_context; p: Z3_params; k: Z3_symbol; v: cdouble) {.libz3.}
proc Z3_params_set_symbol*(c: Z3_context; p: Z3_params; k: Z3_symbol; v: Z3_symbol) {.libz3.}
proc Z3_params_to_string*(c: Z3_context; p: Z3_params): Z3_string {.libz3.}
proc Z3_params_validate*(c: Z3_context; p: Z3_params; d: Z3_param_descrs) {.libz3.}

# Parameter Descriptions
# ======================

proc Z3_param_descrs_inc_ref*(c: Z3_context; p: Z3_param_descrs) {.libz3.}
proc Z3_param_descrs_dec_ref*(c: Z3_context; p: Z3_param_descrs) {.libz3.}
proc Z3_param_descrs_get_kind*(c: Z3_context; p: Z3_param_descrs; n: Z3_symbol): Z3_param_kind {.libz3.}
proc Z3_param_descrs_size*(c: Z3_context; p: Z3_param_descrs): cuint {.libz3.}
proc Z3_param_descrs_get_name*(c: Z3_context; p: Z3_param_descrs; i: cuint): Z3_symbol {.libz3.}
proc Z3_param_descrs_get_documentation*(c: Z3_context; p: Z3_param_descrs; s: Z3_symbol): Z3_string {.libz3.}
proc Z3_param_descrs_to_string*(c: Z3_context; p: Z3_param_descrs): Z3_string {.libz3.}

# Symbols
# =======

proc Z3_mk_int_symbol*(c: Z3_context; i: cint): Z3_symbol {.libz3.}
proc Z3_mk_string_symbol*(c: Z3_context; s: Z3_string): Z3_symbol {.libz3.}

# Sorts
# =====

proc Z3_mk_uninterpreted_sort*(c: Z3_context; s: Z3_symbol): Z3_sort {.libz3.}
proc Z3_mk_bool_sort*(c: Z3_context): Z3_sort {.libz3.}
proc Z3_mk_int_sort*(c: Z3_context): Z3_sort {.libz3.}
proc Z3_mk_real_sort*(c: Z3_context): Z3_sort {.libz3.}
proc Z3_mk_bv_sort*(c: Z3_context; sz: cuint): Z3_sort {.libz3.}
proc Z3_mk_finite_domain_sort*(c: Z3_context; name: Z3_symbol; size: uint64): Z3_sort {.libz3.}
proc Z3_mk_array_sort*(c: Z3_context; domain: Z3_sort; range: Z3_sort): Z3_sort {.libz3.}
proc Z3_mk_array_sort_n*(c: Z3_context; n: cuint; domain: ptr Z3_sort; range: Z3_sort): Z3_sort {.libz3.}
proc Z3_mk_tuple_sort*(c: Z3_context; mk_tuple_name: Z3_symbol; num_fields: cuint; field_names: carray[Z3_symbol]; field_sorts: carray[Z3_sort]; mk_tuple_decl: ptr Z3_func_decl; proj_decl: carray[Z3_func_decl]): Z3_sort {.libz3.}
proc Z3_mk_enumeration_sort*(c: Z3_context; name: Z3_symbol; n: cuint; enum_names: carray[Z3_symbol]; enum_consts: carray[Z3_func_decl]; enum_testers: carray[Z3_func_decl]): Z3_sort {.libz3.}
proc Z3_mk_list_sort*(c: Z3_context; name: Z3_symbol; elem_sort: Z3_sort; nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl: ptr Z3_func_decl): Z3_sort {.libz3.}
proc Z3_mk_constructor*(c: Z3_context; name, recognizer: Z3_symbol; num_fields: cuint; field_names: carray[Z3_symbol]; sorts: carray[Z3_sort_opt]; sort_refs: carray[cuint]): Z3_constructor {.libz3.}
proc Z3_del_constructor*(c: Z3_context; constr: Z3_constructor) {.libz3.}
proc Z3_mk_datatype*(c: Z3_context; name: Z3_symbol; num_constructors: cuint; constructors: carray[Z3_constructor]): Z3_sort {.libz3.}
proc Z3_mk_constructor_list*(c: Z3_context; num_constructors: cuint; constructors: carray[Z3_constructor]): Z3_constructor_list {.libz3.}
proc Z3_del_constructor_list*(c: Z3_context; clist: Z3_constructor_list) {.libz3.}
proc Z3_mk_datatypes*(c: Z3_context; num_sorts: cuint; sort_names: carray[Z3_symbol]; sorts: carray[Z3_sort]; constructor_lists: carray[Z3_constructor_list]) {.libz3.}
proc Z3_query_constructor*(c: Z3_context; constr: Z3_constructor; num_fields: cuint; constructor, tester: ptr Z3_func_decl; accessors: carray[Z3_func_decl]) {.libz3.}

# Constants and Applications
# ==========================

proc Z3_mk_func_decl*(c: Z3_context; s: Z3_symbol; domain_size: cuint; domain: carray[Z3_sort]; range: Z3_sort): Z3_func_decl {.libz3.}
proc Z3_mk_app*(c: Z3_context; d: Z3_func_decl; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_mk_const*(c: Z3_context; s: Z3_symbol; ty: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_fresh_decl*(c: Z3_context; prefix: Z3_string; domain_size: cuint; domain: carray[Z3_sort]; range: Z3_sort): Z3_func_decl {.libz3.}
proc Z3_mk_fresh_const*(c: Z3_context; prefix: Z3_string; ty: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_rec_func_decl*(c: Z3_context; s: Z3_symbol; domain_size: cuint; domain: carray[Z3_sort]; range: Z3_sort): Z3_func_decl {.libz3.}
proc Z3_add_rec_def*(c: Z3_context; f: Z3_func_decl; n: cuint; args: carray[Z3_ast]; body: Z3_ast) {.libz3.}

# Propositional Logic and Equality
# ================================

proc Z3_mk_true*(c: Z3_context): Z3_ast {.libz3.}
proc Z3_mk_false*(c: Z3_context): Z3_ast {.libz3.}
proc Z3_mk_eq*(c: Z3_context; l, r: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_distinct*(c: Z3_context; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_mk_not*(c: Z3_context; a: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_ite*(c: Z3_context; t1, t2, t3: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_iff*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_implies*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_xor*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_and*(c: Z3_context; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_mk_or*(c: Z3_context; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}

# Integers and Reals
# ==================

proc Z3_mk_add*(c: Z3_context; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_mk_mul*(c: Z3_context; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_mk_sub*(c: Z3_context; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_mk_unary_minus*(c: Z3_context; arg: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_div*(c: Z3_context; arg1, arg2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_mod*(c: Z3_context; arg1, arg2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_rem*(c: Z3_context; arg1, arg2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_power*(c: Z3_context; arg1, arg2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_lt*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_le*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_gt*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_ge*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_int2real*(c: Z3_context; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_real2int*(c: Z3_context; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_is_int*(c: Z3_context; t1: Z3_ast): Z3_ast {.libz3.}

# Bit-vectors
# ===========

proc Z3_mk_bvnot*(c: Z3_context; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvredand*(c: Z3_context; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvredor*(c: Z3_context; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvand*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvor*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvxor*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvnand*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvnor*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvxnor*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvneg*(c: Z3_context; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvadd*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsub*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvmul*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvudiv*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsdiv*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvurem*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsrem*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsmod*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvult*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvslt*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvule*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsle*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvuge*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsge*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvugt*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsgt*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_concat*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_extract*(c: Z3_context; high, low: cuint; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_sign_ext*(c: Z3_context; i: cuint; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_zero_ext*(c: Z3_context; i: cuint; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_repeat*(c: Z3_context; i: cuint; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvshl*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvlshr*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvashr*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_rotate_left*(c: Z3_context; i: cuint; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_rotate_right*(c: Z3_context; i: cuint; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_ext_rotate_left*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_ext_rotate_right*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_int2bv*(c: Z3_context; n: cuint; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bv2int*(c: Z3_context; t1: Z3_ast; is_signed: bool): Z3_ast {.libz3.}
proc Z3_mk_bvadd_no_overflow*(c: Z3_context; t1, t2: Z3_ast; is_signed: bool): Z3_ast {.libz3.}
proc Z3_mk_bvadd_no_underflow*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsub_no_overflow*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvsub_no_underflow*(c: Z3_context; t1, t2: Z3_ast; is_signed: bool): Z3_ast {.libz3.}
proc Z3_mk_bvsdiv_no_overflow*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvneg_no_overflow*(c: Z3_context; t1: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_bvmul_no_overflow*(c: Z3_context; t1, t2: Z3_ast; is_signed: bool): Z3_ast {.libz3.}
proc Z3_mk_bvmul_no_underflow*(c: Z3_context; t1, t2: Z3_ast): Z3_ast {.libz3.}

# Arrays
# ======

proc Z3_mk_select*(c: Z3_context; a, i: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_select_n*(c: Z3_context; a: Z3_ast; n: cuint; idxs: ptr Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_store*(c: Z3_context; a, i, v: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_store_n*(c: Z3_context; a: Z3_ast; n: cuint; idxs: ptr Z3_ast, v: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_const_array*(c: Z3_context; domain: Z3_sort; v: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_map*(c: Z3_context; f: Z3_func_decl; n: cuint; args: ptr Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_array_default*(c: Z3_context; array: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_as_array*(c: Z3_context; f: Z3_func_decl): Z3_ast {.libz3.}

# Sets
# ====

proc Z3_mk_set_sort*(c: Z3_context; ty: Z3_sort): Z3_sort {.libz3.}
proc Z3_mk_empty_set*(c: Z3_context; domain: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_full_set*(c: Z3_context; domain: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_set_add*(c: Z3_context; set, elem: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_set_del*(c: Z3_context; set, elem: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_set_union*(c: Z3_context; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_mk_set_intersect*(c: Z3_context; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_mk_set_difference*(c: Z3_context; arg1, arg2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_set_complement*(c: Z3_context; arg: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_set_member*(c: Z3_context; elem, set: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_set_subset*(c: Z3_context; arg1, arg2: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_array_ext*(c: Z3_context; arg1, arg2: Z3_ast): Z3_ast {.libz3.}

# Numerals
# ========

proc Z3_mk_numeral*(c: Z3_context; numeral: Z3_string; ty: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_real*(c: Z3_context; num, den: cint): Z3_ast {.libz3.}
proc Z3_mk_int*(c: Z3_context; v: cint; ty: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_unsigned_int*(c: Z3_context; v: cuint; ty: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_int64*(c: Z3_context; v: int64; ty: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_unsigned_int64*(c: Z3_context; v: uint64; ty: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_bv_numeral*(c: Z3_context; sz: cuint; bits: ptr bool): Z3_ast {.libz3.}

# Sequences and regular expressions
# =================================


# Quantifiers
# ===========

proc Z3_mk_pattern*(c: Z3_context; num_patterns: cuint; terms: carray[Z3_ast]): Z3_pattern {.libz3.}
proc Z3_mk_bound*(c: Z3_context; index: cuint; ty: Z3_sort): Z3_ast {.libz3.}
proc Z3_mk_forall*(c: Z3_context; weight, num_patterns: cuint; patterns: carray[Z3_pattern]; num_decls: cuint; sorts: carray[Z3_sort]; decl_names: carray[Z3_symbol]; body: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_exists*(c: Z3_context; weight, num_patterns: cuint; patterns: carray[Z3_pattern]; num_decls: cuint; sorts: carray[Z3_sort]; decl_names: carray[Z3_symbol]; body: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_forall_const*(c: Z3_context; weight, num_bound: cuint; bound: carray[Z3_app]; num_patterns: cuint; patterns: carray[Z3_pattern]; body: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_exists_const*(c: Z3_context; weight, num_bound: cuint; bound: carray[Z3_app]; num_patterns: cuint; patterns: carray[Z3_pattern]; body: Z3_ast): Z3_ast {.libz3.}
proc Z3_mk_quantifier_const*(c: Z3_context; is_forall: bool; weight, num_bound: cuint; bound: carray[Z3_app]; num_patterns: cuint; patterns: carray[Z3_pattern]; body: Z3_ast): Z3_ast {.libz3.}

# Accessors
# =========

proc Z3_is_eq_sort*(c: Z3_context; s1, s2: Z3_sort): bool {.libz3.}
proc Z3_is_eq_func_decl*(c: Z3_context; f1, f2: Z3_func_decl): bool {.libz3.}
proc Z3_is_eq_ast*(c: Z3_context; t1, t2: Z3_ast): bool {.libz3.}
proc Z3_get_ast_hash*(c: Z3_context; a: Z3_ast): cuint {.libz3.}
proc Z3_get_sort*(c: Z3_context; a: Z3_ast): Z3_sort {.libz3.}
proc Z3_is_app*(c: Z3_context; a: Z3_ast): bool {.libz3.}
proc Z3_is_numeral_ast*(c: Z3_context; a: Z3_ast): bool {.libz3.}
proc Z3_to_app*(c: Z3_context; a: Z3_ast): Z3_app {.libz3.}
proc Z3_get_numeral_double*(c: Z3_context; a: Z3_ast): cdouble {.libz3.}
proc Z3_get_numeral_int*(c: Z3_context; v: Z3_ast; i: ptr cint): bool {.libz3.}
proc Z3_get_numeral_uint*(c: Z3_context; v: Z3_ast; u: ptr cuint): bool {.libz3.}
proc Z3_get_numeral_uint64*(c: Z3_context; v: Z3_ast; i: ptr uint64): bool {.libz3.}
proc Z3_get_numeral_int64*(c: Z3_context; v: Z3_ast; i: ptr int64): bool {.libz3.}
proc Z3_simplify*(c: Z3_context; a: Z3_ast): Z3_ast {.libz3.}
proc Z3_simplify_ex*(c: Z3_context; a: Z3_ast; p: Z3_params): Z3_ast {.libz3.}

# Modifiers
# =========

proc Z3_update_term*(c: Z3_context; a: Z3_ast; num_args: cuint; args: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_substitute*(c: Z3_context; a: Z3_ast; num_exprs: cuint; `from`, to: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_substitute_vars*(c: Z3_context; a: Z3_ast; num_exprs: cuint; to: carray[Z3_ast]): Z3_ast {.libz3.}
proc Z3_translate*(source: Z3_context; a: Z3_ast; target: Z3_context): Z3_ast {.libz3.}

# Models
# ======

proc Z3_mk_model*(c: Z3_context): Z3_model {.libz3.}
proc Z3_model_inc_ref*(c: Z3_context; m: Z3_model) {.libz3.}
proc Z3_model_dec_ref*(c: Z3_context; m: Z3_model) {.libz3.}
proc Z3_model_eval*(c: Z3_context; m: Z3_model; t: Z3_ast; model_completion: bool; v: ptr Z3_ast): bool {.libz3.}
proc Z3_model_get_const_interp*(c: Z3_context; m: Z3_model; a: Z3_func_decl): Z3_ast {.libz3.}
proc Z3_model_has_interp*(c: Z3_context; m: Z3_model; a: Z3_func_decl): bool {.libz3.}
proc Z3_model_get_func_interp*(c: Z3_context; m: Z3_model; f: Z3_func_decl): Z3_func_interp {.libz3.}
proc Z3_model_get_num_consts*(c: Z3_context; m: Z3_model): cuint {.libz3.}
proc Z3_model_get_const_decl*(c: Z3_context; m: Z3_model; i: cuint): Z3_func_decl {.libz3.}
proc Z3_model_get_num_funcs*(c: Z3_context; m: Z3_model): cuint {.libz3.}
proc Z3_model_get_func_decl*(c: Z3_context; m: Z3_model; i: cuint): Z3_func_decl {.libz3.}
proc Z3_model_get_num_sorts*(c: Z3_context; m: Z3_model): cuint {.libz3.}
proc Z3_model_get_sort*(c: Z3_context; m: Z3_model; i: cuint): Z3_sort {.libz3.}
proc Z3_model_get_sort_universe*(c: Z3_context; m: Z3_model; s: Z3_sort): Z3_ast_vector {.libz3.}
proc Z3_model_translate*(c: Z3_context; m: Z3_model; dst: Z3_context): Z3_model {.libz3.}

# Interaction logging
# ===================

proc Z3_open_log*(filename: Z3_string): bool {.libz3.}
proc Z3_append_log*(string: Z3_string) {.libz3.}
proc Z3_close_log* {.libz3.}
proc Z3_toggle_warning_messages*(enabled: bool) {.libz3.}

# String conversion
# =================

proc Z3_set_ast_print_mode*(c: Z3_context; mode: Z3_ast_print_mode) {.libz3.}
proc Z3_ast_to_string*(c: Z3_context; a: Z3_ast): Z3_string {.libz3.}
proc Z3_pattern_to_string*(c: Z3_context; p: Z3_pattern): Z3_string {.libz3.}
proc Z3_sort_to_string*(c: Z3_context; s: Z3_sort): Z3_string {.libz3.}
proc Z3_func_decl_to_string*(c: Z3_context; d: Z3_func_decl): Z3_string {.libz3.}
proc Z3_model_to_string*(c: Z3_context; m: Z3_model): Z3_string {.libz3.}
proc Z3_benchmark_to_smtlib_string*(c: Z3_context; name, logic, status, attributes: Z3_string; num_assumptions: cuint; assumptions: carray[Z3_ast]; formula: Z3_ast): Z3_string {.libz3.}

# Parser interface
# ================

proc Z3_parse_smtlib2_string*(c: Z3_context; str: Z3_string; num_sorts: cuint; sort_names: carray[Z3_symbol]; sorts: carray[Z3_sort]; num_decls: cuint; decl_names: carray[Z3_symbol]; decls: carray[Z3_func_decl]): Z3_ast_vector {.libz3.}
proc Z3_parse_smtlib2_file*(c: Z3_context; file_name: Z3_string; num_sorts: cuint; sort_names: carray[Z3_symbol]; sorts: carray[Z3_sort]; num_decls: cuint; decl_names: carray[Z3_symbol]; decls: carray[Z3_func_decl]): Z3_ast_vector {.libz3.}
proc Z3_eval_smtlib2_string*(c: Z3_context; str: Z3_string): Z3_string {.libz3.}

# Error Handling
# ==============

proc Z3_get_error_code*(c: Z3_context): Z3_error_code {.libz3.}
proc Z3_set_error_handler*(c: Z3_context; h: Z3_error_handler) {.libz3.}
proc Z3_set_error*(c: Z3_context; e: Z3_error_code) {.libz3.}
proc Z3_get_error_msg*(c: Z3_context; err: Z3_error_code): Z3_string {.libz3.}

# Miscellaneous
# =============

proc Z3_get_version*(major, minor, build_number, revision_number: ptr cuint) {.libz3.}
proc Z3_get_full_version*: Z3_string {.libz3.}
proc Z3_enable_trace*(tag: Z3_string) {.libz3.}
proc Z3_disable_trace*(tag: Z3_string) {.libz3.}
proc Z3_reset_memory* {.libz3.}
proc Z3_finalize_memory* {.libz3.}

# Goals
# =====


# Tactics and Probes
# ==================


# Solvers
# =======

proc Z3_mk_solver*(c: Z3_context): Z3_solver {.libz3.}
proc Z3_mk_simple_solver*(c: Z3_context): Z3_solver {.libz3.}
proc Z3_mk_solver_for_logic*(c: Z3_context; logic: Z3_symbol): Z3_solver {.libz3.}
proc Z3_mk_solver_from_tactic*(c: Z3_context; t: Z3_tactic): Z3_solver {.libz3.}
proc Z3_solver_translate*(source: Z3_context; s: Z3_solver; target: Z3_context): Z3_solver {.libz3.}
proc Z3_solver_import_model_converter*(ctx: Z3_context; src, dst: Z3_solver) {.libz3.}
proc Z3_solver_get_help*(c: Z3_context; s: Z3_solver): Z3_string {.libz3.}
proc Z3_solver_get_param_descrs*(c: Z3_context; s: Z3_solver): Z3_param_descrs {.libz3.}
proc Z3_solver_set_params*(c: Z3_context; s: Z3_solver; p: Z3_params) {.libz3.}
proc Z3_solver_inc_ref*(c: Z3_context; s: Z3_solver) {.libz3.}
proc Z3_solver_dec_ref*(c: Z3_context; s: Z3_solver) {.libz3.}
proc Z3_solver_push*(c: Z3_context; s: Z3_solver) {.libz3.}
proc Z3_solver_pop*(c: Z3_context; s: Z3_solver; n: cuint) {.libz3.}
proc Z3_solver_reset*(c: Z3_context; s: Z3_solver) {.libz3.}
proc Z3_solver_get_num_scopes*(c: Z3_context; s: Z3_solver): cuint {.libz3.}
proc Z3_solver_assert*(c: Z3_context; s: Z3_solver; a: Z3_ast) {.libz3.}
proc Z3_solver_assert_and_track*(c: Z3_context; s: Z3_solver; a: Z3_ast; p: Z3_ast) {.libz3.}
proc Z3_solver_from_file*(c: Z3_context; s: Z3_solver; file_name: Z3_string) {.libz3.}
proc Z3_solver_from_string*(c: Z3_context; s: Z3_solver; file_name: Z3_string) {.libz3.}
proc Z3_solver_get_assertions*(c: Z3_context; s: Z3_solver): Z3_ast_vector {.libz3.}
proc Z3_solver_get_units*(c: Z3_context; s: Z3_solver): Z3_ast_vector {.libz3.}
proc Z3_solver_get_trail*(c: Z3_context; s: Z3_solver): Z3_ast_vector {.libz3.}
proc Z3_solver_get_non_units*(c: Z3_context; s: Z3_solver): Z3_ast_vector {.libz3.}
proc Z3_solver_get_levels*(c: Z3_context; s: Z3_solver; literals: Z3_ast_vector; sz: cuint; levels: carray[cuint]) {.libz3.}
proc Z3_solver_check*(c: Z3_context; s: Z3_solver): Z3_lbool {.libz3.}
proc Z3_solver_check_assumptions*(c: Z3_context; s: Z3_solver; num_assumptions: cuint; assumptions: carray[Z3_ast]): Z3_lbool {.libz3.}

proc Z3_solver_get_model*(c: Z3_context; s: Z3_solver): Z3_model {.libz3.}
proc Z3_solver_get_proof*(c: Z3_context; s: Z3_solver): Z3_ast {.libz3.}
proc Z3_solver_get_unsat_core*(c: Z3_context; s: Z3_solver): Z3_ast_vector {.libz3.}
proc Z3_solver_get_reason_unknown*(c: Z3_context; s: Z3_solver): Z3_string {.libz3.}
proc Z3_solver_get_statistics*(c: Z3_context; s: Z3_solver): Z3_stats {.libz3.}
proc Z3_solver_to_string*(c: Z3_context; s: Z3_solver): Z3_string {.libz3.}
proc Z3_solver_to_dimacs_string*(c: Z3_context; s: Z3_solver): Z3_string {.libz3.}

# Statistics
# ==========

proc Z3_stats_to_string*(c: Z3_context; s: Z3_stats): Z3_string {.libz3.}
proc Z3_stats_inc_ref*(c: Z3_context; s: Z3_stats) {.libz3.}
proc Z3_stats_dec_ref*(c: Z3_context; s: Z3_stats) {.libz3.}
proc Z3_stats_size*(c: Z3_context; s: Z3_stats): cuint {.libz3.}
proc Z3_stats_get_key*(c: Z3_context; s: Z3_stats; idx: cuint): Z3_string {.libz3.}
proc Z3_stats_is_uint*(c: Z3_context; s: Z3_stats; idx: cuint): bool {.libz3.}
proc Z3_stats_is_double*(c: Z3_context; s: Z3_stats; idx: cuint): bool {.libz3.}
proc Z3_stats_get_uint_value*(c: Z3_context; s: Z3_stats; idx: cuint): cuint {.libz3.}
proc Z3_stats_get_double_value*(c: Z3_context; s: Z3_stats; idx: cuint): cdouble {.libz3.}
proc Z3_get_estimated_alloc_size*: uint64 {.libz3.}

# AST vectors
# ===========

proc Z3_mk_ast_vector*(c: Z3_context): Z3_ast_vector {.libz3.}
proc Z3_ast_vector_inc_ref*(c: Z3_context; v: Z3_ast_vector) {.libz3.}
proc Z3_ast_vector_dec_ref*(c: Z3_context; v: Z3_ast_vector) {.libz3.}
proc Z3_ast_vector_size*(c: Z3_context; v: Z3_ast_vector): cuint {.libz3.}
proc Z3_ast_vector_get*(c: Z3_context; v: Z3_ast_vector; i: cuint): Z3_ast {.libz3.}
proc Z3_ast_vector_set*(c: Z3_context; v: Z3_ast_vector; i: cuint; a: Z3_ast) {.libz3.}
proc Z3_ast_vector_resize*(c: Z3_context; v: Z3_ast_vector; n: cuint) {.libz3.}
proc Z3_ast_vector_push*(c: Z3_context; v: Z3_ast_vector; a: Z3_ast) {.libz3.}
proc Z3_ast_vector_translate*(s: Z3_context; v: Z3_ast_vector; t: Z3_context): Z3_ast_vector {.libz3.}
proc Z3_ast_vector_to_string*(c: Z3_context; v: Z3_ast_vector): Z3_string {.libz3.}

# AST maps
# ========


# Fixedpoint facilities
# =====================


# Floating-Point Arithmetic
# =========================


# Z3-specific floating-point extensions
# =====================================


# Optimization facilities
# =======================


# Polynomials
# ===========

proc Z3_polynomial_subresultants*(c: Z3_context; p, q, x: Z3_ast): Z3_ast_vector {.libz3.}

# Real Closed Fields
# ==================


# Algebraic Numbers
# =================
