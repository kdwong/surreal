// Lean compiler output
// Module: Surreal.surreal
// Imports: public import Init public import Mathlib.Tactic.Linarith public import Mathlib.Data.List.MinMax public import Mathlib.Order.Basic public import Surreal.game
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
LEAN_EXPORT lean_object* l_Surreal_right___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instCoeSurrealGame;
LEAN_EXPORT lean_object* l___private_Surreal_surreal_0__instReprGame_repr_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeSurrealGame___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Surreal_right(lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_surreal_0__instReprGame_repr_match__1_splitter___redArg(lean_object*, lean_object*);
extern lean_object* l_zero;
LEAN_EXPORT lean_object* l_Surreal_left___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instCoeSurrealGame___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Surreal_left(lean_object*);
LEAN_EXPORT lean_object* l_sr__zero;
LEAN_EXPORT lean_object* l_instCoeSurrealGame___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
static lean_object* _init_l_instCoeSurrealGame() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instCoeSurrealGame___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instCoeSurrealGame___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instCoeSurrealGame___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Surreal_left(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Surreal_left___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Surreal_left(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Surreal_right(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Surreal_right___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Surreal_right(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_sr__zero() {
_start:
{
lean_object* x_1; 
x_1 = l_zero;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_surreal_0__instReprGame_repr_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_surreal_0__instReprGame_repr_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Surreal_surreal_0__instReprGame_repr_match__1_splitter___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Tactic_Linarith(uint8_t builtin);
lean_object* initialize_Mathlib_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Mathlib_Order_Basic(uint8_t builtin);
lean_object* initialize_Surreal_game(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Surreal_surreal(uint8_t builtin) {
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
l_instCoeSurrealGame = _init_l_instCoeSurrealGame();
lean_mark_persistent(l_instCoeSurrealGame);
l_sr__zero = _init_l_sr__zero();
lean_mark_persistent(l_sr__zero);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
