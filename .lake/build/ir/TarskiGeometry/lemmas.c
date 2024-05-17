// Lean compiler output
// Module: TarskiGeometry.Lemmas
// Imports: Init Mathlib.ModelTheory.Semantics
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_formula_u2083(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_formula_u2084(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1;
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_FirstOrder_Language_Relations_formula(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Fin_cases(x_4, lean_box(0), x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___rarg___boxed), 3, 0);
return x_4;
}
}
static lean_object* _init_l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1;
x_10 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_10);
x_13 = lean_alloc_closure((void*)(l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___rarg___boxed), 3, 2);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_FirstOrder_Language_Relations_boundedFormula_u2083___elambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2083___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_FirstOrder_Language_Relations_boundedFormula_u2083(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(3u);
x_5 = l_Fin_cases(x_4, lean_box(0), x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1;
x_11 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_7);
lean_closure_set(x_13, 2, x_11);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_13);
x_16 = lean_alloc_closure((void*)(l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___rarg___boxed), 3, 2);
lean_closure_set(x_16, 0, x_5);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(4u);
x_18 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_FirstOrder_Language_Relations_boundedFormula_u2084___elambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_boundedFormula_u2084___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_FirstOrder_Language_Relations_boundedFormula_u2084(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_formula_u2083(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1;
x_9 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_11);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_FirstOrder_Language_Relations_formula(x_1, lean_box(0), x_14, x_3, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_FirstOrder_Language_Relations_formula_u2084(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1;
x_10 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_10);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_12);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_14);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_FirstOrder_Language_Relations_formula(x_1, lean_box(0), x_17, x_3, x_16);
return x_18;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_ModelTheory_Semantics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TarskiGeometry_Lemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_ModelTheory_Semantics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1 = _init_l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1();
lean_mark_persistent(l_FirstOrder_Language_Relations_boundedFormula_u2083___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
