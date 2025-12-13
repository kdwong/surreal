// Lean compiler output
// Module: Surreal.game
// Imports: public import Init public import Mathlib.Tactic.Linarith public import Mathlib.Data.List.MinMax
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game_right(lean_object*);
static lean_object* l_half___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_game_0__Game_left_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zero_x27;
static lean_object* l_one___closed__0;
LEAN_EXPORT lean_object* l_Game_right___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_maximum___at___00Game_birthday_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Game_left___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_maximum___at___00Game_birthday_spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_game_0__List_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_zero_x27___closed__0;
LEAN_EXPORT lean_object* l_List_maximum___at___00Game_birthday_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_game_0__Game_left_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_half;
LEAN_EXPORT lean_object* l_Game_left(lean_object*);
LEAN_EXPORT lean_object* l_List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Game_birthday_spec__0(lean_object*, lean_object*);
lean_object* l_List_argAux___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_minus__one___closed__1;
static lean_object* l_half___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_one;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_zero_x27___closed__1;
LEAN_EXPORT lean_object* l_zero;
LEAN_EXPORT lean_object* l_Game_birthday(lean_object*);
LEAN_EXPORT lean_object* l_minus__one;
LEAN_EXPORT lean_object* l_Game_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Surreal_game_0__List_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TriGame_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Game_ctorIdx___boxed(lean_object*);
static lean_object* l_zero___closed__0;
static lean_object* l_minus__one___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_TriGame_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Game_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Game_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Game_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Game_left(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Game_left___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Game_left(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Game_right(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Game_right___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Game_right(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_zero___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_zero() {
_start:
{
lean_object* x_1; 
x_1 = l_zero___closed__0;
return x_1;
}
}
static lean_object* _init_l_minus__one___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_zero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_minus__one___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_minus__one___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_minus__one() {
_start:
{
lean_object* x_1; 
x_1 = l_minus__one___closed__1;
return x_1;
}
}
static lean_object* _init_l_one___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_minus__one___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_one() {
_start:
{
lean_object* x_1; 
x_1 = l_one___closed__0;
return x_1;
}
}
static lean_object* _init_l_half___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_one;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_half___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_half___closed__0;
x_2 = l_minus__one___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_half() {
_start:
{
lean_object* x_1; 
x_1 = l_half___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Game_birthday_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Game_birthday(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Game_birthday(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_List_argAux___redArg(x_6, x_2, x_4);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_maximum___at___00Game_birthday_spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_maximum___at___00Game_birthday_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_List_maximum___at___00Game_birthday_spec__1___lam__0___boxed), 1, 0);
x_3 = l_List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game_birthday(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___00Game_birthday_spec__0(x_6, x_8);
x_10 = l_List_mapTR_loop___at___00Game_birthday_spec__0(x_7, x_8);
x_11 = l_List_appendTR___redArg(x_9, x_10);
x_12 = l_List_maximum___at___00Game_birthday_spec__1(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(0u);
x_2 = x_13;
goto block_5;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_2 = x_14;
goto block_5;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_foldl___at___00List_argmax___at___00List_maximum___at___00Game_birthday_spec__1_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_maximum___at___00Game_birthday_spec__1___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_maximum___at___00Game_birthday_spec__1___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_game_0__Game_left_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Surreal_game_0__Game_left_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Surreal_game_0__Game_left_match__1_splitter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_game_0__List_map__unattach_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Surreal_game_0__List_map__unattach_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_5, x_4, lean_box(0));
return x_6;
}
}
static lean_object* _init_l_zero_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_minus__one;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_zero_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_half___closed__0;
x_2 = l_zero_x27___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_zero_x27() {
_start:
{
lean_object* x_1; 
x_1 = l_zero_x27___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_TriGame_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_TriGame_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_TriGame_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Tactic_Linarith(uint8_t builtin);
lean_object* initialize_Mathlib_Data_List_MinMax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Surreal_game(uint8_t builtin) {
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
l_zero___closed__0 = _init_l_zero___closed__0();
lean_mark_persistent(l_zero___closed__0);
l_zero = _init_l_zero();
lean_mark_persistent(l_zero);
l_minus__one___closed__0 = _init_l_minus__one___closed__0();
lean_mark_persistent(l_minus__one___closed__0);
l_minus__one___closed__1 = _init_l_minus__one___closed__1();
lean_mark_persistent(l_minus__one___closed__1);
l_minus__one = _init_l_minus__one();
lean_mark_persistent(l_minus__one);
l_one___closed__0 = _init_l_one___closed__0();
lean_mark_persistent(l_one___closed__0);
l_one = _init_l_one();
lean_mark_persistent(l_one);
l_half___closed__0 = _init_l_half___closed__0();
lean_mark_persistent(l_half___closed__0);
l_half___closed__1 = _init_l_half___closed__1();
lean_mark_persistent(l_half___closed__1);
l_half = _init_l_half();
lean_mark_persistent(l_half);
l_zero_x27___closed__0 = _init_l_zero_x27___closed__0();
lean_mark_persistent(l_zero_x27___closed__0);
l_zero_x27___closed__1 = _init_l_zero_x27___closed__1();
lean_mark_persistent(l_zero_x27___closed__1);
l_zero_x27 = _init_l_zero_x27();
lean_mark_persistent(l_zero_x27);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
