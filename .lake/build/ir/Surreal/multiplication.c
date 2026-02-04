// Lean compiler output
// Module: Surreal.multiplication
// Imports: public import Init public import Mathlib.Tactic.Linarith public import Mathlib.Data.List.MinMax public import Mathlib.Order.Basic public import Surreal.game public import Surreal.surreal public import Surreal.addition
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
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__Game_mul_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Game_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__flatten_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game_mul(lean_object*, lean_object*);
lean_object* l_Game_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__Game_mul_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Surreal_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_flatten___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__Game_mul_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__flatten_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__flatten_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Game_mul_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__Game_mul_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Game_mul_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Game_mul_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__flatten_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_flatten(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_flatten___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_flatten___redArg(x_4);
x_6 = l_List_appendTR___redArg(x_3, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_flatten(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_flatten___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Game_mul_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = l_List_reverse___redArg(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_10 = l_Game_mul(x_1, x_2);
lean_inc(x_8);
lean_inc_ref(x_3);
x_11 = l_Game_mul(x_3, x_8);
x_12 = l_Game_add(x_10, x_11);
lean_inc_ref(x_1);
x_13 = l_Game_mul(x_1, x_8);
x_14 = l_Game_neg(x_13);
x_15 = l_Game_add(x_12, x_14);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_15);
{
lean_object* _tmp_3 = x_9;
lean_object* _tmp_4 = x_4;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_19 = l_Game_mul(x_1, x_2);
lean_inc(x_17);
lean_inc_ref(x_3);
x_20 = l_Game_mul(x_3, x_17);
x_21 = l_Game_add(x_19, x_20);
lean_inc_ref(x_1);
x_22 = l_Game_mul(x_1, x_17);
x_23 = l_Game_neg(x_22);
x_24 = l_Game_add(x_21, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
x_4 = x_18;
x_5 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Game_mul_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = l_List_reverse___redArg(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_box(0);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_11 = l_List_mapTR_loop___at___00Game_mul_spec__0(x_8, x_1, x_2, x_3, x_10);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_11);
{
lean_object* _tmp_3 = x_9;
lean_object* _tmp_4 = x_4;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_box(0);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_16 = l_List_mapTR_loop___at___00Game_mul_spec__0(x_13, x_1, x_2, x_3, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_4 = x_14;
x_5 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Game_mul_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = l_List_reverse___redArg(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_box(0);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_11 = l_List_mapTR_loop___at___00Game_mul_spec__0(x_8, x_1, x_2, x_3, x_10);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_11);
x_12 = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Game_mul_spec__1_spec__1(x_1, x_2, x_3, x_9, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_box(0);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_16 = l_List_mapTR_loop___at___00Game_mul_spec__0(x_13, x_1, x_2, x_3, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_18 = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Game_mul_spec__1_spec__1(x_1, x_2, x_3, x_14, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Game_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_box(0);
lean_inc(x_3);
lean_inc(x_5);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_8 = l_List_mapTR_loop___at___00Game_mul_spec__1(x_2, x_1, x_5, x_3, x_7);
x_9 = l_flatten___redArg(x_8);
lean_inc(x_4);
lean_inc(x_6);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_10 = l_List_mapTR_loop___at___00Game_mul_spec__1(x_2, x_1, x_6, x_4, x_7);
x_11 = l_flatten___redArg(x_10);
x_12 = l_List_appendTR___redArg(x_9, x_11);
lean_inc(x_3);
lean_inc(x_6);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_13 = l_List_mapTR_loop___at___00Game_mul_spec__1(x_2, x_1, x_6, x_3, x_7);
x_14 = l_flatten___redArg(x_13);
x_15 = l_List_mapTR_loop___at___00Game_mul_spec__1(x_2, x_1, x_5, x_4, x_7);
x_16 = l_flatten___redArg(x_15);
x_17 = l_List_appendTR___redArg(x_14, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__Game_mul_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__Game_mul_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__Game_mul_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__Game_mul_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Surreal_multiplication_0__Game_mul_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__flatten_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__flatten_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Surreal_multiplication_0__flatten_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__flatten_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Surreal_multiplication_0__flatten_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_multiplication_0__flatten_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Surreal_multiplication_0__flatten_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Surreal_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Game_mul(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Tactic_Linarith(uint8_t builtin);
lean_object* initialize_Mathlib_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Mathlib_Order_Basic(uint8_t builtin);
lean_object* initialize_Surreal_game(uint8_t builtin);
lean_object* initialize_Surreal_surreal(uint8_t builtin);
lean_object* initialize_Surreal_addition(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Surreal_multiplication(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Surreal_game(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Surreal_surreal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Surreal_addition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
