#!/usr/bin/env python3
# Generates export/CCLib/IntegersInst.lean
import os
HW = "(by decide)"
# (name, binders, statement, proof args, required ops)
L = [
 # ranges
 ("unsigned_range", "(x : T)", "0 ≤ unsigned x ∧ unsigned x < modulus", "x", ""),
 ("unsigned_range_2", "(x : T)", "0 ≤ unsigned x ∧ unsigned x ≤ max_unsigned", "x", ""),
 ("signed_range", "(x : T)", "min_signed ≤ signed x ∧ signed x ≤ max_signed", "HW x", ""),
 ("repr_unsigned", "(x : T)", "repr (unsigned x) = x", "x", ""),
 ("repr_signed", "(x : T)", "repr (signed x) = x", "x", ""),
 ("unsigned_repr_eq", "(z : Z)", "unsigned (repr z) = z % modulus", "z", ""),
 ("unsigned_repr", "{z : Z} (h1 : 0 ≤ z) (h2 : z ≤ max_unsigned)", "unsigned (repr z) = z", "h1 h2", ""),
 ("signed_repr", "{z : Z} (h1 : min_signed ≤ z) (h2 : z ≤ max_signed)", "signed (repr z) = z", "HW h1 h2", ""),
 ("signed_eq_unsigned", "(x : T) (h : unsigned x ≤ max_signed)", "signed x = unsigned x", "HW x h", ""),
 ("signed_positive", "(x : T)", "0 ≤ signed x ↔ unsigned x ≤ max_signed", "HW x", ""),
 ("unsigned_inj", "{x y : T} (h : unsigned x = unsigned y)", "x = y", "h", ""),
 ("signed_inj", "{x y : T} (h : signed x = signed y)", "x = y", "h", ""),
 # eqm
 ("eqm_iff_emod", "{x y : Z}", "eqm x y ↔ x % modulus = y % modulus", "", ""),
 ("eqm_refl", "(x : Z)", "eqm x x", "x", ""),
 ("eqm_sym", "{x y : Z} (h : eqm x y)", "eqm y x", "h", ""),
 ("eqm_trans", "{x y z : Z} (h1 : eqm x y) (h2 : eqm y z)", "eqm x z", "h1 h2", ""),
 ("eqm_add", "{a b c d : Z} (h1 : eqm a b) (h2 : eqm c d)", "eqm (a + c) (b + d)", "h1 h2", ""),
 ("eqm_neg", "{x y : Z} (h : eqm x y)", "eqm (-x) (-y)", "h", ""),
 ("eqm_sub", "{a b c d : Z} (h1 : eqm a b) (h2 : eqm c d)", "eqm (a - c) (b - d)", "h1 h2", ""),
 ("eqm_mult", "{a b c d : Z} (h1 : eqm a c) (h2 : eqm b d)", "eqm (a * b) (c * d)", "h1 h2", ""),
 ("eqm_samerepr", "{x y : Z} (h : eqm x y)", "(repr x : T) = repr y", "h", ""),
 ("eqm_unsigned_repr", "(z : Z)", "eqm z (unsigned (repr z : T))", "z", ""),
 ("eqm_repr_eq", "{x : Z} {y : T} (h : eqm x (unsigned y))", "repr x = y", "h", ""),
 ("eqm_signed_unsigned", "(x : T)", "eqm (signed x) (unsigned x)", "x", ""),
 # eq
 ("eq_spec", "(x y : T)", "eq x y = true ↔ x = y", "x y", ""),
 ("eq_true", "(x : T)", "eq x x = true", "x", ""),
 ("eq_false", "{x y : T} (h : x ≠ y)", "eq x y = false", "h", ""),
 ("eq_sym", "(x y : T)", "eq x y = eq y x", "x y", ""),
 ("same_if_eq", "{x y : T} (h : eq x y = true)", "x = y", "h", ""),
 # constants
 ("unsigned_zero", "", "unsigned zero = 0", "", ""),
 ("unsigned_one", "", "unsigned one = 1", "HW", ""),
 ("unsigned_mone", "", "unsigned mone = modulus - 1", "", ""),
 ("signed_zero", "", "signed zero = 0", "", ""),
 ("signed_mone", "", "signed mone = -1", "HW", ""),
 ("one_not_zero", "", "one ≠ zero", "HW", ""),
 ("mone_ne_zero", "", "mone ≠ zero", "HW", ""),
 ("repr_zero", "", "repr 0 = zero", "", ""),
 ("repr_one", "", "repr 1 = one", "", ""),
 ("repr_mone", "", "repr (-1) = mone", "", ""),
 # add
 ("add_unsigned", "(x y : T)", "add x y = repr (unsigned x + unsigned y)", "x y", ""),
 ("add_signed", "(x y : T)", "add x y = repr (signed x + signed y)", "x y", ""),
 ("add_commut", "(x y : T)", "add x y = add y x", "x y", ""),
 ("add_zero", "(x : T)", "add x zero = x", "x", ""),
 ("add_zero_l", "(x : T)", "add zero x = x", "x", ""),
 ("add_assoc", "(x y z : T)", "add (add x y) z = add x (add y z)", "x y z", ""),
 ("add_permut", "(x y z : T)", "add x (add y z) = add y (add x z)", "x y z", ""),
 ("add_neg_zero", "(x : T)", "add x (neg x) = zero", "x", ""),
 ("unsigned_add_carry", "(x y : T)", "unsigned (add x y) = unsigned x + unsigned y - unsigned (add_carry x y zero) * modulus", "x y", "carry"),
 ("unsigned_add_either", "(x y : T)", "unsigned (add x y) = unsigned x + unsigned y ∨ unsigned (add x y) = unsigned x + unsigned y - modulus", "x y", ""),
 ("repr_add", "(a b : Z)", "(repr (a + b) : T) = add (repr a) (repr b)", "a b", ""),
 # neg / sub
 ("neg_repr", "(z : Z)", "neg (repr z : T) = repr (-z)", "z", ""),
 ("neg_zero", "", "neg zero = zero", "", ""),
 ("neg_involutive", "(x : T)", "neg (neg x) = x", "x", ""),
 ("neg_add_distr", "(x y : T)", "neg (add x y) = add (neg x) (neg y)", "x y", ""),
 ("sub_zero_l", "(x : T)", "sub zero x = neg x", "x", ""),
 ("sub_zero_r", "(x : T)", "sub x zero = x", "x", ""),
 ("sub_add_opp", "(x y : T)", "sub x y = add x (neg y)", "x y", ""),
 ("sub_idem", "(x : T)", "sub x x = zero", "x", ""),
 ("sub_add_l", "(x y z : T)", "sub (add x y) z = add (sub x z) y", "x y z", ""),
 ("sub_add_r", "(x y z : T)", "sub x (add y z) = add (sub x z) (neg y)", "x y z", ""),
 ("sub_shifted", "(x y z : T)", "sub (add x z) (add y z) = sub x y", "x y z", ""),
 ("sub_unsigned", "(x y : T)", "sub x y = repr (unsigned x - unsigned y)", "x y", ""),
 ("sub_signed", "(x y : T)", "sub x y = repr (signed x - signed y)", "x y", ""),
 ("repr_sub", "(a b : Z)", "(repr (a - b) : T) = sub (repr a) (repr b)", "a b", ""),
 ("unsigned_sub_borrow", "(x y : T)", "unsigned (sub x y) = unsigned x - unsigned y + unsigned (sub_borrow x y zero) * modulus", "x y", "carry"),
 # mul
 ("mul_unsigned", "(x y : T)", "mul x y = repr (unsigned x * unsigned y)", "x y", ""),
 ("mul_signed", "(x y : T)", "mul x y = repr (signed x * signed y)", "x y", ""),
 ("repr_mul", "(a b : Z)", "(repr (a * b) : T) = mul (repr a) (repr b)", "a b", ""),
 ("mul_commut", "(x y : T)", "mul x y = mul y x", "x y", ""),
 ("mul_zero", "(x : T)", "mul x zero = zero", "x", ""),
 ("mul_one", "(x : T)", "mul x one = x", "x", ""),
 ("mul_mone", "(x : T)", "mul x mone = neg x", "x", ""),
 ("mul_assoc", "(x y z : T)", "mul (mul x y) z = mul x (mul y z)", "x y z", ""),
 ("mul_add_distr_l", "(x y z : T)", "mul (add x y) z = add (mul x z) (mul y z)", "x y z", ""),
 ("mul_add_distr_r", "(x y z : T)", "mul x (add y z) = add (mul x y) (mul x z)", "x y z", ""),
 ("neg_mul_distr_l", "(x y : T)", "neg (mul x y) = mul (neg x) y", "x y", ""),
 ("neg_mul_distr_r", "(x y : T)", "neg (mul x y) = mul x (neg y)", "x y", ""),
 # comparisons
 ("ltu_def", "(x y : T)", "ltu x y = decide (unsigned x < unsigned y)", "x y", ""),
 ("ltu_iff", "(x y : T)", "ltu x y = true ↔ unsigned x < unsigned y", "x y", ""),
 ("lt_def", "(x y : T)", "lt x y = decide (signed x < signed y)", "x y", ""),
 ("lt_iff", "(x y : T)", "lt x y = true ↔ signed x < signed y", "x y", ""),
 ("ltu_inv", "{x y : T} (h : ltu x y = true)", "0 ≤ unsigned x ∧ unsigned x < unsigned y", "h", ""),
 ("lt_irrefl", "(x : T)", "lt x x = false", "x", ""),
 ("ltu_irrefl", "(x : T)", "ltu x x = false", "x", ""),
 ("ltu_zero", "(x : T)", "ltu x zero = false", "x", ""),
 ("not_lt", "(x y : T)", "(!(lt y x)) = (lt x y || eq x y)", "x y", ""),
 ("not_ltu", "(x y : T)", "(!(ltu y x)) = (ltu x y || eq x y)", "x y", ""),
 ("lt_not", "(x y : T)", "lt y x = (!(lt x y) && !(eq x y))", "x y", ""),
 ("ltu_not", "(x y : T)", "ltu y x = (!(ltu x y) && !(eq x y))", "x y", ""),
 ("negate_cmp", "(c : Comparison) (x y : T)", "cmp c.negate x y = !(cmp c x y)", "c x y", ""),
 ("negate_cmpu", "(c : Comparison) (x y : T)", "cmpu c.negate x y = !(cmpu c x y)", "c x y", ""),
 ("swap_cmp", "(c : Comparison) (x y : T)", "cmp c.swap x y = cmp c y x", "c x y", ""),
 ("swap_cmpu", "(c : Comparison) (x y : T)", "cmpu c.swap x y = cmpu c y x", "c x y", ""),
 ("translate_eq", "(x y d : T)", "eq (add x d) (add y d) = eq x y", "x y d", ""),
 ("translate_ltu", "{x y d : T} (hx : unsigned x + unsigned d ≤ max_unsigned) (hy : unsigned y + unsigned d ≤ max_unsigned)", "ltu (add x d) (add y d) = ltu x y", "hx hy", ""),
 ("translate_cmpu", "(c : Comparison) {x y d : T} (hx : unsigned x + unsigned d ≤ max_unsigned) (hy : unsigned y + unsigned d ≤ max_unsigned)", "cmpu c (add x d) (add y d) = cmpu c x y", "c hx hy", ""),
 # division
 ("unsigned_divu", "(x y : T)", "unsigned (divu x y) = unsigned x / unsigned y", "x y", ""),
 ("unsigned_modu", "(x y : T)", "unsigned (modu x y) = unsigned x % unsigned y", "x y", ""),
 ("divu_unsigned", "(x y : T)", "divu x y = repr (unsigned x / unsigned y)", "x y", ""),
 ("modu_unsigned", "(x y : T)", "modu x y = repr (unsigned x % unsigned y)", "x y", ""),
 ("modu_divu_Euclid", "(x y : T)", "x = add (mul (divu x y) y) (modu x y)", "x y", ""),
 ("modu_divu", "(x y : T)", "modu x y = sub x (mul (divu x y) y)", "x y", ""),
 ("modu_bound", "(x y : T) (h : y ≠ zero)", "unsigned (modu x y) < unsigned y", "x y h", ""),
 ("divu_one", "(x : T)", "divu x one = x", "x", ""),
 ("modu_one", "(x : T)", "modu x one = zero", "x", ""),
 ("divs_signed", "(x y : T)", "divs x y = repr ((signed x).tdiv (signed y))", "x y", ""),
 ("mods_signed", "(x y : T)", "mods x y = repr ((signed x).tmod (signed y))", "x y", ""),
 ("mods_divs_Euclid", "(x y : T)", "x = add (mul (divs x y) y) (mods x y)", "x y", ""),
 ("mods_divs", "(x y : T)", "mods x y = sub x (mul (divs x y) y)", "x y", ""),
 ("signed_mods", "(x y : T)", "signed (mods x y) = (signed x).tmod (signed y)", "x y", ""),
 # bits
 ("bits_above", "(x : T) {i : Nat} (h : WS ≤ i)", "testbit x i = false", "x h", ""),
 ("same_bits_eq", "{x y : T} (h : ∀ i, i < WS → testbit x i = testbit y i)", "x = y", "h", ""),
 ("bits_zero", "(i : Nat)", "testbit zero i = false", "i", ""),
 ("bits_mone", "{i : Nat} (h : i < WS)", "testbit mone i = true", "h", ""),
 ("bits_and", "(x y : T) (i : Nat)", "testbit (and x y) i = (testbit x i && testbit y i)", "x y i", ""),
 ("bits_or", "(x y : T) (i : Nat)", "testbit (or x y) i = (testbit x i || testbit y i)", "x y i", ""),
 ("bits_xor", "(x y : T) (i : Nat)", "testbit (xor x y) i = (testbit x i ^^ testbit y i)", "x y i", ""),
 ("bits_not", "(x : T) {i : Nat} (h : i < WS)", "testbit (not x) i = !(testbit x i)", "x h", ""),
 ("and_commut", "(x y : T)", "and x y = and y x", "x y", ""),
 ("and_assoc", "(x y z : T)", "and (and x y) z = and x (and y z)", "x y z", ""),
 ("and_zero", "(x : T)", "and x zero = zero", "x", ""),
 ("and_zero_l", "(x : T)", "and zero x = zero", "x", ""),
 ("and_mone", "(x : T)", "and x mone = x", "x", ""),
 ("and_mone_l", "(x : T)", "and mone x = x", "x", ""),
 ("and_idem", "(x : T)", "and x x = x", "x", ""),
 ("or_commut", "(x y : T)", "or x y = or y x", "x y", ""),
 ("or_assoc", "(x y z : T)", "or (or x y) z = or x (or y z)", "x y z", ""),
 ("or_zero", "(x : T)", "or x zero = x", "x", ""),
 ("or_zero_l", "(x : T)", "or zero x = x", "x", ""),
 ("or_mone", "(x : T)", "or x mone = mone", "x", ""),
 ("or_idem", "(x : T)", "or x x = x", "x", ""),
 ("and_or_distrib", "(x y z : T)", "and x (or y z) = or (and x y) (and x z)", "x y z", ""),
 ("and_or_distrib_l", "(x y z : T)", "and (or x y) z = or (and x z) (and y z)", "x y z", ""),
 ("or_and_distrib", "(x y z : T)", "or x (and y z) = and (or x y) (or x z)", "x y z", ""),
 ("or_and_distrib_l", "(x y z : T)", "or (and x y) z = and (or x z) (or y z)", "x y z", ""),
 ("and_or_absorb", "(x y : T)", "and x (or x y) = x", "x y", ""),
 ("or_and_absorb", "(x y : T)", "or x (and x y) = x", "x y", ""),
 ("xor_commut", "(x y : T)", "xor x y = xor y x", "x y", ""),
 ("xor_assoc", "(x y z : T)", "xor (xor x y) z = xor x (xor y z)", "x y z", ""),
 ("xor_zero", "(x : T)", "xor x zero = x", "x", ""),
 ("xor_zero_l", "(x : T)", "xor zero x = x", "x", ""),
 ("xor_idem", "(x : T)", "xor x x = zero", "x", ""),
 ("and_xor_distrib", "(x y z : T)", "and x (xor y z) = xor (and x y) (and x z)", "x y z", ""),
 ("xor_is_zero", "(x y : T)", "xor x y = zero ↔ x = y", "x y", ""),
 ("not_involutive", "(x : T)", "not (not x) = x", "x", ""),
 ("not_zero", "", "not zero = mone", "", ""),
 ("not_mone", "", "not mone = zero", "", ""),
 ("not_or_and_not", "(x y : T)", "not (or x y) = and (not x) (not y)", "x y", ""),
 ("not_and_or_not", "(x y : T)", "not (and x y) = or (not x) (not y)", "x y", ""),
 ("and_not_self", "(x : T)", "and x (not x) = zero", "x", ""),
 ("or_not_self", "(x : T)", "or x (not x) = mone", "x", ""),
 ("xor_not_self", "(x : T)", "xor x (not x) = mone", "x", ""),
 ("not_eq_xor_mone", "(x : T)", "not x = xor x mone", "x", ""),
 ("neg_not", "(x : T)", "neg x = add (not x) one", "x", ""),
 ("not_neg", "(x : T)", "not x = add (neg x) mone", "x", ""),
 ("sub_add_not", "(x y : T)", "sub x y = add (add x (not y)) one", "x y", ""),
 # shifts
 ("bits_shl", "(x y : T) {i : Nat} (hi : i < WS)", "testbit (shl x y) i = if i < y.toNat then false else testbit x (i - y.toNat)", "x y hi", ""),
 ("bits_shru", "(x y : T) {i : Nat} (hi : i < WS)", "testbit (shru x y) i = if i + y.toNat < WS then testbit x (i + y.toNat) else false", "x y hi", ""),
 ("bits_shr", "(x y : T) {i : Nat} (hi : i < WS)", "testbit (shr x y) i = testbit x (if i + y.toNat < WS then i + y.toNat else WS - 1)", "x y hi", ""),
 ("shl_zero", "(x : T)", "shl x zero = x", "x", ""),
 ("shru_zero", "(x : T)", "shru x zero = x", "x", ""),
 ("shr_zero", "(x : T)", "shr x zero = x", "x", ""),
 ("shl_zero_l", "(y : T)", "shl zero y = zero", "y", ""),
 ("shru_zero_l", "(y : T)", "shru zero y = zero", "y", ""),
 ("shr_zero_l", "(y : T)", "shr zero y = zero", "y", ""),
 ("shl_shl", "(x y z : T) (h : y.toNat + z.toNat < 2 ^ WS)", "shl (shl x y) z = shl x (add y z)", "x y z h", ""),
 ("shru_shru", "(x y z : T) (h : y.toNat + z.toNat < 2 ^ WS)", "shru (shru x y) z = shru x (add y z)", "x y z h", ""),
 ("shr_shr", "(x y z : T) (h : y.toNat + z.toNat < 2 ^ WS)", "shr (shr x y) z = shr x (add y z)", "x y z h", ""),
 ("and_shl", "(x y z : T)", "and (shl x z) (shl y z) = shl (and x y) z", "x y z", ""),
 ("or_shl", "(x y z : T)", "or (shl x z) (shl y z) = shl (or x y) z", "x y z", ""),
 ("xor_shl", "(x y z : T)", "xor (shl x z) (shl y z) = shl (xor x y) z", "x y z", ""),
 ("and_shru", "(x y z : T)", "and (shru x z) (shru y z) = shru (and x y) z", "x y z", ""),
 ("or_shru", "(x y z : T)", "or (shru x z) (shru y z) = shru (or x y) z", "x y z", ""),
 ("xor_shru", "(x y z : T)", "xor (shru x z) (shru y z) = shru (xor x y) z", "x y z", ""),
 ("and_shr", "(x y z : T)", "and (shr x z) (shr y z) = shr (and x y) z", "x y z", ""),
 ("or_shr", "(x y z : T)", "or (shr x z) (shr y z) = shr (or x y) z", "x y z", ""),
 ("xor_shr", "(x y z : T)", "xor (shr x z) (shr y z) = shr (xor x y) z", "x y z", ""),
 ("shl_mul", "(x y : T)", "shl x y = mul x (shl one y)", "x y", ""),
 ("shl_mul_two_p", "(x y : T)", "shl x y = mul x (repr ((2 : Z) ^ y.toNat))", "x y", ""),
 ("shru_div_two_p", "(x y : T)", "shru x y = repr (unsigned x / (2 : Z) ^ y.toNat)", "x y", ""),
 ("shr_div_two_p", "(x y : T)", "shr x y = repr (signed x / (2 : Z) ^ y.toNat)", "x y", ""),
 ("rol_zero", "(x : T)", "rol x zero = x", "x", "rot"),
 ("ror_zero", "(x : T)", "ror x zero = x", "x", "rot"),
 # extensions
 ("bits_zero_ext", "(n : Nat) (x : T) (i : Nat)", "testbit (zero_ext n x) i = (decide (i < n) && testbit x i)", "n x i", ""),
 ("zero_ext_above", "{n : Nat} (h : WS ≤ n) (x : T)", "zero_ext n x = x", "h x", ""),
 ("zero_ext_idem", "(n : Nat) (x : T)", "zero_ext n (zero_ext n x) = zero_ext n x", "n x", ""),
 ("zero_ext_widen", "{n n' : Nat} (h : n ≤ n') (x : T)", "zero_ext n' (zero_ext n x) = zero_ext n x", "h x", ""),
 ("zero_ext_narrow", "{n n' : Nat} (h : n ≤ n') (x : T)", "zero_ext n (zero_ext n' x) = zero_ext n x", "h x", ""),
 ("zero_ext_mod", "(n : Nat) (x : T)", "unsigned (zero_ext n x) = unsigned x % (2 : Z) ^ n", "n x", ""),
 ("zero_ext_range", "(n : Nat) (x : T)", "unsigned (zero_ext n x) < (2 : Z) ^ n", "n x", ""),
 ("bits_sign_ext", "{n : Nat} (hn : 0 < n) (x : T) {i : Nat} (hi : i < WS)", "testbit (sign_ext n x) i = testbit x (if i < n then i else n - 1)", "hn x hi", ""),
 ("sign_ext_above", "{n : Nat} (hn : 0 < n) (h : WS ≤ n) (x : T)", "sign_ext n x = x", "hn h x", ""),
 ("sign_ext_widen", "{n n' : Nat} (hn : 0 < n) (h : n ≤ n') (x : T)", "sign_ext n' (sign_ext n x) = sign_ext n x", "hn h x", ""),
 ("sign_ext_idem", "{n : Nat} (hn : 0 < n) (x : T)", "sign_ext n (sign_ext n x) = sign_ext n x", "hn x", ""),
 ("sign_ext_narrow", "{n n' : Nat} (hn : 0 < n) (h : n ≤ n') (x : T)", "sign_ext n (sign_ext n' x) = sign_ext n x", "hn h x", ""),
 ("zero_ext_sign_ext", "{n n' : Nat} (hn : 0 < n) (h : n ≤ n') (x : T)", "zero_ext n (sign_ext n' x) = zero_ext n x", "hn h x", ""),
 ("sign_ext_zero_ext", "{n n' : Nat} (hn : 0 < n) (h : n ≤ n') (x : T)", "sign_ext n (zero_ext n' x) = sign_ext n x", "hn h x", ""),
]

INST = [
 ("Int", "Int", "32", {"carry", "rot"}),
 ("Int64", "Int64", "64", {"carry", "rot"}),
 ("Ptrofs", "Ptrofs", "Archi.ptrWordsize", set()),
]

HEADER = '''/-
  The theorems of `IntegersLemmas`, `IntegersBits` and `IntegersShifts`,
  restated for the concrete module `{ns}` ({desc}), under the names CompCert
  uses (`{ns}.add_commut`, `{ns}.unsigned_repr`, …).

  Each statement is about the module's own operations (`{ns}.add`, …), so it
  can be used with `rw`; the proof is the generic `MI` theorem, with the
  word-size side conditions (`0 < w`) discharged by `decide`.

  Generated by `export/tools/gen_integers_inst.py`; to add a theorem, prove
  the generic `MI` version first, then add a line to that script.
-/
import CCLib.IntegersShifts

namespace CC
namespace Integers
'''
DESC = {"Int": "32 bits", "Int64": "64 bits", "Ptrofs": "`Archi.ptrWordsize` bits"}
for (ns, T, WS, ops) in INST:
    out = [HEADER.format(ns=ns, desc=DESC[ns])]
    out.append(f"namespace {ns}\n")
    out.append(f"/-- `{ns}.eqm`: congruence modulo `{ns}.modulus`. -/\ndef eqm (x y : Z) : Prop := MI.eqm {WS} x y\n")
    for (name, binders, stmt, args, req) in L:
        if req and req not in ops:
            continue
        b = binders.replace("(x : T)", f"(x : {T})")
        b = b.replace(": T)", f": {T})").replace(": T}", f": {T}}}").replace("WS", WS)
        st = stmt.replace(": T)", f": {T})").replace("WS", WS)
        a = args.replace("HW", HW)
        proof = f"MI.{name}" + (f" {a}" if a else "")
        out.append(f"theorem {name} {b} :\n    {st} :=\n  {proof}\n")
    out.append(f"end {ns}\nend Integers\nend CC\n")
    open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "CCLib", f"Integers{ns}.lean"), "w").write("\n".join(out))
