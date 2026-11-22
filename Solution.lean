/-
Copyright 2026 The Formal Conjectures Authors and Yuto Nakahara.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Normalized convolution of $\binom{6k}{3k}\binom{3k}{k}$

The sequence $a(n)$ is defined by
$$a(n) = \frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}
  \binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}.$$

*References:*
- [A189286](https://oeis.org/A189286)
- T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?",
  [arXiv:2608.11941](https://arxiv.org/abs/2608.11941) [cs.AI], 2026.
-/

@[expose] public section

namespace OeisA189286

/-- The term $\binom{6k}{3k}\binom{3k}{k}$ appearing in the sum. -/
def tTerm (k : ℕ) : ℚ := ((6 * k).choose (3 * k) * (3 * k).choose k : ℕ)

/--
The sequence $a(n)$ given by
$\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}
  \binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
-/
def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n + 1), tTerm k * tTerm (n - k)) /
    (((2 * (n : ℚ)) - 1) * ((3 * n).choose n : ℚ))

theorem a_0 : a 0 = -1 := by decide +kernel

theorem a_1 : a 1 = 40 := by decide +kernel

theorem a_2 : a 2 = 696 := by decide +kernel

theorem a_3 : a 3 = 23408 := by decide +kernel

theorem a_4 : a 4 = 969496 := by decide +kernel

private def tNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

private def sNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), tNat k * tNat (n - k)

private lemma tNat_pos (k : ℕ) : 0 < tNat k :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

private lemma sNat_pos (n : ℕ) : 0 < sNat n :=
  Finset.sum_pos (fun k _ => Nat.mul_pos (tNat_pos k) (tNat_pos (n - k)))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

private lemma denom_pos {n : ℕ} (hn : 0 < n) : 0 < (2 * n - 1) * (3 * n).choose n :=
  Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

private lemma a_eq_div_nat {n : ℕ} (hn : 0 < n) :
    a n = (sNat n : ℚ) / (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) := by
  unfold a sNat tTerm
  have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp only [tNat, Nat.cast_sum, Nat.cast_mul, hsub]

private lemma tNat_mul_factorials (k : ℕ) :
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial = (6 * k).factorial := by
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 6 * k) (k := 3 * k) (by omega)
    rwa [show 6 * k - 3 * k = 3 * k by omega] at this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := k) (by omega)
    rwa [show 3 * k - k = 2 * k by omega] at this
  calc
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial
        = (6 * k).choose (3 * k) * (3 * k).factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial) := by
            unfold tNat; ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

private lemma choose_3n_mul_factorials (n : ℕ) :
    (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
  have := Nat.choose_mul_factorial_mul_factorial (n := 3 * n) (k := n) (by omega)
  rwa [show 3 * n - n = 2 * n by omega] at this

private def fStep (q r : ℕ) : ℕ := 6 * r / q - 3 * r / q - 2 * r / q

private def gStep (q r : ℕ) : ℕ := 3 * r / q - 2 * r / q

private lemma nat_div_eq_of_le_lt {q m j : ℕ} (hq : 0 < q)
    (h1 : j * q ≤ m) (h2 : m < (j + 1) * q) : m / q = j :=
  le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq).mpr h2))
    ((Nat.le_div_iff_mul_le hq).mpr h1)

private lemma fStep_spec {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    3 * r / q + 2 * r / q ≤ 6 * r / q ∧
    fStep q r = if 6 * r < q then 0 else if 6 * r < 5 * q then 1 else 2 := by
  unfold fStep
  by_cases h1 : 6 * r < q
  · have h6 : 6 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h2 : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    simp [h1, h6, h3, h2]
  · by_cases h2 : 6 * r < 2 * q
    · have h6 : 6 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      rw [ite_eq_right h1, ite_eq_left (by omega)]
      omega
    · by_cases h3 : 6 * r < 3 * q
      · have h6 : 6 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [ite_eq_right h1, ite_eq_left (by omega)]
        omega
      · by_cases h4 : 6 * r < 4 * q
        · have h6 : 6 * r / q = 3 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          rw [ite_eq_right h1, ite_eq_left (by omega)]
          omega
        · by_cases h5 : 6 * r < 5 * q
          · have h6 : 6 * r / q = 4 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            rw [ite_eq_right h1, ite_eq_left h5]
            omega
          · have h6 : 6 * r / q = 5 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            rw [ite_eq_right h1, ite_eq_right h5]
            omega

private lemma gStep_spec {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    2 * r / q ≤ 3 * r / q ∧
    gStep q r = if (2 * q ≤ 6 * r ∧ 6 * r < 3 * q) ∨ 4 * q ≤ 6 * r then 1 else 0 := by
  unfold gStep
  by_cases h1 : 6 * r < 2 * q
  · have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h2 : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    rw [ite_eq_right (by omega)]
    omega
  · by_cases h2 : 6 * r < 3 * q
    · have h3 : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      rw [ite_eq_left (by omega)]
      omega
    · by_cases h3 : 6 * r < 4 * q
      · have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [ite_eq_right (by omega)]
        omega
      · have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [ite_eq_left (by omega)]
        omega

private lemma div_six_eq {q a : ℕ} (hq : 0 < q) :
    6 * a / q = 3 * a / q + 2 * a / q + a / q + fStep q (a % q) := by
  have hmul : ∀ c : ℕ, c * a / q = c * (a / q) + c * (a % q) / q := by
    intro c
    have hda : q * (a / q) + a % q = a := Nat.div_add_mod a q
    have heq : c * a = c * (a % q) + q * (c * (a / q)) := by
      calc c * a = c * (q * (a / q) + a % q) := by rw [hda]
        _ = c * (a % q) + q * (c * (a / q)) := by ring
    rw [heq, Nat.add_mul_div_left _ _ hq]
    omega
  have hle := (fStep_spec hq (Nat.mod_lt a hq)).1
  have h6 := hmul 6
  have h3 := hmul 3
  have h2 := hmul 2
  unfold fStep
  omega

private lemma div_three_eq {q a : ℕ} (hq : 0 < q) :
    3 * a / q = 2 * a / q + a / q + gStep q (a % q) := by
  have hmul : ∀ c : ℕ, c * a / q = c * (a / q) + c * (a % q) / q := by
    intro c
    have hda : q * (a / q) + a % q = a := Nat.div_add_mod a q
    have heq : c * a = c * (a % q) + q * (c * (a / q)) := by
      calc c * a = c * (q * (a / q) + a % q) := by rw [hda]
        _ = c * (a % q) + q * (c * (a / q)) := by ring
    rw [heq, Nat.add_mul_div_left _ _ hq]
    omega
  have hle := (gStep_spec hq (Nat.mod_lt a hq)).1
  have h3 := hmul 3
  have h2 := hmul 2
  unfold gStep
  omega

private lemma padicValNat_tNat_eq_sum {p k b : ℕ} [hp : Fact p.Prime]
    (hb : Nat.log p (6 * k) < b) :
    padicValNat p (tNat k) = ∑ i ∈ Finset.Ico 1 b, fStep (p ^ i) (k % p ^ i) := by
  have hfac := congrArg (padicValNat p) (tNat_mul_factorials k)
  rw [padicValNat.mul
        (mul_ne_zero (mul_ne_zero (tNat_pos k).ne' (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (mul_ne_zero (tNat_pos k).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (tNat_pos k).ne' (Nat.factorial_ne_zero _)] at hfac
  rw [padicValNat_factorial hb,
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 b, 6 * k / p ^ i =
      ∑ i ∈ Finset.Ico 1 b, (3 * k / p ^ i + 2 * k / p ^ i + k / p ^ i +
        fStep (p ^ i) (k % p ^ i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_six_eq (pow_pos hp.out.pos i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hfac
  omega

private lemma padicValNat_choose_3n_eq_sum {p n b : ℕ} [hp : Fact p.Prime]
    (hb : Nat.log p (3 * n) < b) :
    padicValNat p ((3 * n).choose n) = ∑ i ∈ Finset.Ico 1 b, gStep (p ^ i) (n % p ^ i) := by
  have hfac := congrArg (padicValNat p) (choose_3n_mul_factorials n)
  rw [padicValNat.mul (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _)] at hfac
  rw [padicValNat_factorial hb,
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 b, 3 * n / p ^ i =
      ∑ i ∈ Finset.Ico 1 b, (2 * n / p ^ i + n / p ^ i + gStep (p ^ i) (n % p ^ i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_three_eq (pow_pos hp.out.pos i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hfac
  omega

private lemma padicValNat_eq_sum_ite_dvd {p x b : ℕ} [hp : Fact p.Prime]
    (hx : 0 < x) (hb : Nat.log p x < b) :
    padicValNat p x = ∑ i ∈ Finset.Ico 1 b, if p ^ i ∣ x then 1 else 0 := by
  have hr : padicValNat p x < b := lt_of_le_of_lt (padicValNat_le_nat_log x) hb
  have hfilt : (Finset.Ico 1 b).filter (fun i => p ^ i ∣ x) =
      Finset.Ico 1 (padicValNat p x + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, padicValNat_dvd_iff_le hx.ne']
    omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
      hfilt, Nat.card_Ico]
  omega

private lemma gStep_le_fStep_add {q k m : ℕ} (hq : 0 < q) :
    gStep q ((k + m) % q) ≤ fStep q (k % q) + fStep q (m % q) := by
  have hfk := (fStep_spec hq (Nat.mod_lt k hq)).2
  have hfm := (fStep_spec hq (Nat.mod_lt m hq)).2
  have hgn := (gStep_spec hq (Nat.mod_lt (k + m) hq)).2
  have hmod : (k + m) % q = (k % q + m % q) % q := Nat.add_mod k m q
  by_cases hkm : k % q + m % q < q
  · rw [Nat.mod_eq_of_lt hkm] at hmod
    rw [hmod] at hgn ⊢
    split_ifs at hfk hfm hgn <;> omega
  · have hsub : (k + m) % q = k % q + m % q - q := by
      have hklt := Nat.mod_lt k hq
      have hmlt := Nat.mod_lt m hq
      rw [hmod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hgn ⊢
    have hklt := Nat.mod_lt k hq
    have hmlt := Nat.mod_lt m hq
    split_ifs at hfk hfm hgn <;> omega

private lemma two_mul_mod_of_dvd {q n : ℕ} (hn : 0 < n) (hq : 2 ≤ q) (hdiv : q ∣ 2 * n - 1) :
    2 * (n % q) = q + 1 := by
  rcases hdiv with ⟨c, hc⟩
  have hr : n % q < q := Nat.mod_lt n (by omega)
  have hdivmod : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have h2n : 2 * n = q * c + 1 := by omega
  have heq : q * c + 1 = 2 * (q * (n / q)) + 2 * (n % q) := by linarith
  have h1 : c < 2 * (n / q) + 2 := by nlinarith
  have h2 : 2 * (n / q) ≤ c := by
    by_contra hlt
    have hle : c + 1 ≤ 2 * (n / q) := by omega
    have hmul : q * c + q ≤ 2 * (q * (n / q)) := by
      calc q * c + q = q * (c + 1) := by ring
        _ ≤ q * (2 * (n / q)) := Nat.mul_le_mul_left q hle
        _ = 2 * (q * (n / q)) := by ring
    omega
  have hne : c ≠ 2 * (n / q) := by
    intro h
    rw [h] at heq
    have : 2 * (n % q) = 1 := by linarith
    omega
  have hc_eq : c = 2 * (n / q) + 1 := by omega
  rw [hc_eq] at heq
  linarith

private lemma dvd_of_two_mul_mod {q n : ℕ} (hn : 0 < n) (hmod : 2 * (n % q) = q + 1) :
    q ∣ 2 * n - 1 := by
  refine ⟨2 * (n / q) + 1, ?_⟩
  have hdivmod : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have : 2 * n = q * (2 * (n / q) + 1) + 1 := by linarith
  omega

private lemma gStep_add_one_le_fStep_add {q k m : ℕ} (hq : 5 ≤ q) (hn : 0 < k + m)
    (hdiv : q ∣ 2 * (k + m) - 1) :
    1 + gStep q ((k + m) % q) ≤ fStep q (k % q) + fStep q (m % q) := by
  have hqpos : 0 < q := by omega
  have h2 := two_mul_mod_of_dvd hn (by omega) hdiv
  have hgn := (gStep_spec hqpos (Nat.mod_lt (k + m) hqpos)).2
  have hg0 : gStep q ((k + m) % q) = 0 := by
    rw [hgn, ite_eq_right (by omega)]
  rw [hg0, add_zero]
  have hfk := (fStep_spec hqpos (Nat.mod_lt k hqpos)).2
  have hfm := (fStep_spec hqpos (Nat.mod_lt m hqpos)).2
  by_contra hlt
  have hfk0 : fStep q (k % q) = 0 := by omega
  have hfm0 : fStep q (m % q) = 0 := by omega
  have hksmall : 6 * (k % q) < q := by
    by_contra h
    rw [hfk, ite_eq_right h] at hfk0
    by_cases h5 : 6 * (k % q) < 5 * q
    · rw [ite_eq_left h5] at hfk0; omega
    · rw [ite_eq_right h5] at hfk0; omega
  have hmsmall : 6 * (m % q) < q := by
    by_contra h
    rw [hfm, ite_eq_right h] at hfm0
    by_cases h5 : 6 * (m % q) < 5 * q
    · rw [ite_eq_left h5] at hfm0; omega
    · rw [ite_eq_right h5] at hfm0; omega
  have hmod : (k + m) % q = k % q + m % q := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

private lemma mod_three_mul {q a : ℕ} (hq : 0 < q) :
    a % (3 * q) = ((a / q) % 3) * q + a % q := by
  have h1 : q * (a / q) + a % q = a := Nat.div_add_mod a q
  have h2 : 3 * ((a / q) / 3) + (a / q) % 3 = a / q := Nat.div_add_mod (a / q) 3
  have h3 : (a / q) % 3 < 3 := Nat.mod_lt _ (by omega)
  have h4 : a % q < q := Nat.mod_lt _ hq
  have hlt : ((a / q) % 3) * q + a % q < 3 * q := by nlinarith
  have heq : a = ((a / q) % 3 * q + a % q) + (3 * q) * ((a / q) / 3) := by nlinarith
  conv_lhs => rw [heq]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private lemma exists_surplus_base3_aux {k m : ℕ} (hn : 0 < k + m)
    (hk3 : k % 3 = 0) (hm3 : m % 3 = 2) :
    ∃ j ∈ Finset.Ico 2 (padicValNat 3 (2 * (k + m) - 1) + 2),
      (if 3 ^ j ∣ 2 * (k + m) - 1 then 1 else 0) + gStep (3 ^ j) ((k + m) % 3 ^ j) + 1 ≤
        fStep (3 ^ j) (k % 3 ^ j) + fStep (3 ^ j) (m % 3 ^ j) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set n := k + m
  set r := padicValNat 3 (2 * n - 1)
  have h3dvd : 3 ∣ 2 * n - 1 := by
    refine dvd_of_two_mul_mod hn ?_
    have : n % 3 = (k % 3 + m % 3) % 3 := Nat.add_mod k m 3
    omega
  have hr1 : 1 ≤ r := one_le_padicValNat_of_dvd (by omega) h3dvd
  by_contra hnone
  push Not at hnone
  have hstep : ∀ j, 1 ≤ j → j ≤ r → k % 3 ^ j = 0 ∧ 2 * (m % 3 ^ j) = 3 ^ j + 1 := by
    intro j hj1 hjr
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hj0 : j = 0
      · subst hj0
        simpa using ⟨hk3, by omega⟩
      · have ⟨hkj, hmj⟩ := ih (by omega) (by omega)
        set q := 3 ^ j
        have hqpos : 0 < q := pow_pos (by omega : 0 < 3) j
        have h3q : 3 ^ (j + 1) = 3 * q := by rw [pow_succ']
        have h3q_pos : 0 < 3 ^ (j + 1) := pow_pos (by omega : 0 < 3) (j + 1)
        have h3q_ge : 5 ≤ 3 ^ (j + 1) := by
          have : 3 ^ 2 ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hdvd_next : 3 ^ (j + 1) ∣ 2 * n - 1 :=
          (padicValNat_dvd_iff_le (p := 3) (by omega)).mpr hjr
        have hgn0 : gStep (3 ^ (j + 1)) (n % 3 ^ (j + 1)) = 0 := by
          have h2n := two_mul_mod_of_dvd hn (by omega) hdvd_next
          have hgs := (gStep_spec h3q_pos (Nat.mod_lt n h3q_pos)).2
          rw [hgs, ite_eq_right (by omega)]
        have hbound := hnone (j + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        rw [ite_eq_left hdvd_next, hgn0, add_zero] at hbound
        have hk_next : k % (3 * q) = ((k / q) % 3) * q := by
          rw [mod_three_mul hqpos, hkj, add_zero]
        have hm_next : m % (3 * q) = ((m / q) % 3) * q + m % q := mod_three_mul hqpos
        have hfm_ge : 1 ≤ fStep (3 ^ (j + 1)) (m % 3 ^ (j + 1)) := by
          have hfs := (fStep_spec h3q_pos (Nat.mod_lt m h3q_pos)).2
          rw [h3q, hm_next] at hfs ⊢
          have h6m : 3 * q ≤ 6 * (((m / q) % 3) * q + m % q) := by
            have : 0 ≤ ((m / q) % 3) * q := Nat.zero_le _
            omega
          rw [hfs, ite_eq_right (by omega)]
          split_ifs <;> omega
        have hfk_eq0 : fStep (3 ^ (j + 1)) (k % 3 ^ (j + 1)) = 0 := by omega
        have hdk0 : (k / q) % 3 = 0 := by
          have hfs := (fStep_spec h3q_pos (Nat.mod_lt k h3q_pos)).2
          rw [h3q, hk_next] at hfs hfk_eq0
          have hlt : 6 * (((k / q) % 3) * q) < 3 * q := by
            by_contra hge
            rw [hfs, ite_eq_right hge] at hfk_eq0
            by_cases h5 : 6 * (((k / q) % 3) * q) < 5 * (3 * q)
            · rw [ite_eq_left h5] at hfk_eq0; omega
            · rw [ite_eq_right h5] at hfk_eq0; omega
          by_contra hne
          have h1 : 1 ≤ (k / q) % 3 := by omega
          have hmul : 1 * q ≤ ((k / q) % 3) * q := Nat.mul_le_mul_right q h1
          omega
        have hk_zero : k % 3 ^ (j + 1) = 0 := by rw [h3q, hk_next, hdk0, zero_mul]
        have hm_eq : m % 3 ^ (j + 1) = n % 3 ^ (j + 1) := by
          have hmod : n % 3 ^ (j + 1) = (k % 3 ^ (j + 1) + m % 3 ^ (j + 1)) % 3 ^ (j + 1) :=
            Nat.add_mod k m _
          rw [hk_zero, zero_add, Nat.mod_mod] at hmod
          exact hmod.symm
        exact ⟨hk_zero, hm_eq.symm ▸ two_mul_mod_of_dvd hn (by omega) hdvd_next⟩
  have ⟨hkr, hmr⟩ := hstep r hr1 le_rfl
  set q := 3 ^ r
  have hq3 : 3 ≤ q := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by omega) hr1
  have hqpos : 0 < q := by omega
  have h3q : 3 ^ (r + 1) = 3 * q := by rw [pow_succ']
  have hndvd : ¬ 3 ^ (r + 1) ∣ 2 * n - 1 := pow_succ_padicValNat_not_dvd (p := 3) (by omega)
  have hbound := hnone (r + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  rw [ite_eq_right hndvd, zero_add, h3q] at hbound
  set dk := (k / q) % 3
  set dm := (m / q) % 3
  have hdk_lt : dk < 3 := Nat.mod_lt _ (by omega)
  have hdm_lt : dm < 3 := Nat.mod_lt _ (by omega)
  have hk_next : k % (3 * q) = dk * q := by rw [mod_three_mul hqpos, hkr, add_zero]
  have hm_next : m % (3 * q) = dm * q + m % q := mod_three_mul hqpos
  have hn_next : n % (3 * q) = ((dk + dm) % 3) * q + m % q := by
    have hmq_lt : m % q < q := Nat.mod_lt m hqpos
    have h1 : n % (3 * q) = (k % (3 * q) + m % (3 * q)) % (3 * q) := Nat.add_mod k m _
    rw [hk_next, hm_next] at h1
    have h2 : dk * q + (dm * q + m % q) =
        (((dk + dm) % 3) * q + m % q) + (3 * q) * ((dk + dm) / 3) := by
      have := Nat.div_add_mod (dk + dm) 3
      nlinarith
    have h3 : ((dk + dm) % 3) * q + m % q < 3 * q := by
      have : (dk + dm) % 3 < 3 := Nat.mod_lt _ (by omega)
      nlinarith
    rw [h1, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h3]
  have hneq1 : (dk + dm) % 3 ≠ 1 := by
    intro h1
    apply hndvd
    rw [h3q]
    refine dvd_of_two_mul_mod hn ?_
    rw [hn_next, h1]
    omega
  have hfk := (fStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt k (by omega))).2
  have hfm := (fStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt m (by omega))).2
  have hgn := (gStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt n (by omega))).2
  rw [hk_next, hm_next, hn_next] at hbound
  rw [hk_next] at hfk
  rw [hm_next] at hfm
  rw [hn_next] at hgn
  interval_cases dk <;> interval_cases dm <;>
    simp only [Nat.reduceAdd, Nat.reduceMod, zero_mul, one_mul, zero_add] at hneq1 hbound hfk hfm hgn ⊢
  all_goals
    try exact absurd rfl hneq1
  all_goals
    split_ifs at hfk hfm hgn <;> omega

private lemma padicValNat_denom_le_tNat_mul {p n k m : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hkm : k + m = n) :
    padicValNat p ((2 * n - 1) * (3 * n).choose n) ≤ padicValNat p (tNat k * tNat m) := by
  have : Fact p.Prime := ⟨hp⟩
  set b := Nat.log p (6 * n) + 1
  have hb6n : Nat.log p (6 * n) < b := Nat.lt_succ_self _
  have hb6k : Nat.log p (6 * k) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb6m : Nat.log p (6 * m) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb3n : Nat.log p (3 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb2n : Nat.log p (2 * n - 1) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne',
      padicValNat.mul (tNat_pos k).ne' (tNat_pos m).ne',
      padicValNat_eq_sum_ite_dvd (by omega) hb2n,
      padicValNat_choose_3n_eq_sum hb3n,
      padicValNat_tNat_eq_sum hb6k,
      padicValNat_tNat_eq_sum hb6m,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  by_cases h3 : p = 3 ∧ 3 ∣ 2 * n - 1
  · rcases h3 with ⟨rfl, h3dvd⟩
    set L : ℕ → ℕ := fun i => (if 3 ^ i ∣ 2 * n - 1 then 1 else 0) + gStep (3 ^ i) (n % 3 ^ i)
    set R : ℕ → ℕ := fun i => fStep (3 ^ i) (k % 3 ^ i) + fStep (3 ^ i) (m % 3 ^ i)
    change ∑ i ∈ Finset.Ico 1 b, L i ≤ ∑ i ∈ Finset.Ico 1 b, R i
    have hge2 : ∀ i ∈ Finset.Ico 2 b, L i ≤ R i := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      dsimp only [L, R]
      by_cases hd : 3 ^ i ∣ 2 * n - 1
      · rw [ite_eq_left hd, ← hkm]
        have h3i_ge : 5 ≤ 3 ^ i := by
          have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by omega) hi.1
          omega
        exact gStep_add_one_le_fStep_add h3i_ge (by omega) (hkm ▸ hd)
      · rw [ite_eq_right hd, zero_add, ← hkm]
        exact gStep_le_fStep_add (pow_pos (by omega : 0 < 3) i)
    by_cases hL1 : L 1 ≤ R 1
    · refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      by_cases hi1 : i = 1
      · subst hi1; exact hL1
      · exact hge2 i (Finset.mem_Ico.mpr ⟨by omega, hi.2⟩)
    · have h2n3 : n % 3 = 2 := by
        have := two_mul_mod_of_dvd hn (by omega) h3dvd
        omega
      have hL1_val : L 1 = 2 := by
        dsimp only [L]
        rw [pow_one, ite_eq_left h3dvd, h2n3]
        decide
      have hk3_lt : k % 3 < 3 := Nat.mod_lt k (by omega)
      have hm3_lt : m % 3 < 3 := Nat.mod_lt m (by omega)
      have hkm3 : (k % 3 + m % 3) % 3 = 2 := by
        rw [← Nat.add_mod, hkm, h2n3]
      have hfk1 := (fStep_spec (q := 3) (r := k % 3) (by omega) hk3_lt).2
      have hfm1 := (fStep_spec (q := 3) (r := m % 3) (by omega) hm3_lt).2
      have hcases : (k % 3 = 0 ∧ m % 3 = 2) ∨ (k % 3 = 2 ∧ m % 3 = 0) := by
        have hR1 : R 1 < 2 := by omega
        dsimp only [R] at hR1
        rw [pow_one] at hR1
        split_ifs at hfk1 hfm1 <;> omega
      have hR1_val : R 1 = 1 := by
        dsimp only [R]
        rw [pow_one]
        rcases hcases with ⟨hk0, hm2⟩ | ⟨hk2, hm0⟩
        · rw [hk0, hm2]; decide
        · rw [hk2, hm0]; decide
      have hsurplus : ∃ j ∈ Finset.Ico 2 (padicValNat 3 (2 * n - 1) + 2), L j + 1 ≤ R j := by
        rcases hcases with ⟨hk0, hm2⟩ | ⟨hk2, hm0⟩
        · obtain ⟨j, hj, hle⟩ := exists_surplus_base3_aux (k := k) (m := m) (by omega) hk0 hm2
          exact ⟨j, by rwa [hkm] at hj, by simpa only [L, R, hkm] using hle⟩
        · obtain ⟨j, hj, hle⟩ := exists_surplus_base3_aux (k := m) (m := k) (by omega) hm0 hk2
          refine ⟨j, by rwa [add_comm m k, hkm] at hj, ?_⟩
          dsimp only [L, R]
          rw [add_comm m k, hkm] at hle
          omega
      obtain ⟨j, hj_mem, hj_surp⟩ := hsurplus
      rw [Finset.mem_Ico] at hj_mem
      have hr_pow : 3 ^ (padicValNat 3 (2 * n - 1) + 1) ≤ 6 * n := by
        have hpow_dvd : 3 ^ padicValNat 3 (2 * n - 1) ∣ 2 * n - 1 := pow_padicValNat_dvd
        have hle : 3 ^ padicValNat 3 (2 * n - 1) ≤ 2 * n - 1 := Nat.le_of_dvd (by omega) hpow_dvd
        rw [pow_succ']
        omega
      have hr_lt_b : padicValNat 3 (2 * n - 1) + 1 < b :=
        Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by omega) hr_pow)
      have hj_in : j ∈ Finset.Ico 2 b := Finset.mem_Ico.mpr ⟨hj_mem.1, by omega⟩
      have h1b : 1 < b := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot h1b, Finset.sum_eq_sum_Ico_succ_bot h1b]
      rw [← Finset.add_sum_erase _ _ hj_in, ← Finset.add_sum_erase _ _ hj_in]
      have hrest : ∑ i ∈ (Finset.Ico 2 b).erase j, L i ≤ ∑ i ∈ (Finset.Ico 2 b).erase j, R i :=
        Finset.sum_le_sum fun i hi => hge2 i (Finset.mem_of_mem_erase hi)
      omega
  · refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    by_cases hd : p ^ i ∣ 2 * n - 1
    · rw [ite_eq_left hd, ← hkm]
      have hp_dvd : p ∣ 2 * n - 1 := dvd_trans (dvd_pow_self p (by omega)) hd
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hp_dvd
        omega
      have hp3 : p ≠ 3 := fun h3' => h3 ⟨h3', h3' ▸ hp_dvd⟩
      have hp5 : 5 ≤ p := by
        have := hp.two_le
        have hne4 : p ≠ 4 := by intro h4; rw [h4] at hp; exact absurd hp (by decide)
        omega
      have hpi5 : 5 ≤ p ^ i :=
        le_trans hp5 (by simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hi.1)
      exact gStep_add_one_le_fStep_add hpi5 (by omega) (hkm ▸ hd)
    · rw [ite_eq_right hd, zero_add, ← hkm]
      exact gStep_le_fStep_add (pow_pos hp.pos i)

private lemma denom_dvd_tNat_mul {n k m : ℕ} (hn : 0 < n) (hkm : k + m = n) :
    (2 * n - 1) * (3 * n).choose n ∣ tNat k * tNat m := by
  rw [← Nat.factorization_le_iff_dvd (denom_pos hn).ne'
      (Nat.mul_pos (tNat_pos k) (tNat_pos m)).ne']
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact padicValNat_denom_le_tNat_mul hp hn hkm
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma denom_dvd_sNat {n : ℕ} (hn : 0 < n) :
    (2 * n - 1) * (3 * n).choose n ∣ sNat n := by
  unfold sNat
  refine Finset.dvd_sum fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact denom_dvd_tNat_mul hn (Nat.add_sub_of_le hkn)

/--
Conjecture: $a(n)$ is an integer for every $n = 0, 1, 2, \dots$.
- _Zhi-Wei Sun_, Apr 19 2011

Proved in the OEIS Open project, see T. Adamczewski, OEIS Open: How many conjectures can
language models turn into theorems?, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941).
-/
theorem conjecture_1 (n : ℕ) : (a n).den = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [a_0]; rfl
  · obtain ⟨q, hq⟩ := denom_dvd_sNat hn
    have hd : (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (denom_pos hn).ne'
    have han : a n = (q : ℚ) := by
      rw [a_eq_div_nat hn, hq, Nat.cast_mul, mul_div_cancel_left₀ _ hd]
    rw [han]
    exact Rat.den_natCast q


private def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma s2_zero : s2 0 = 0 := by simp [s2]

private lemma s2_two_mul (n : ℕ) : s2 (2 * n) = s2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [s2]
  · unfold s2
    rw [show 2 * n = 0 + 2 * n by omega,
        Nat.digits_add 2 (by omega) 0 n (by omega) (Or.inr hn)]
    simp

private lemma s2_two_mul_add_one (n : ℕ) : s2 (2 * n + 1) = s2 n + 1 := by
  unfold s2
  rw [show 2 * n + 1 = 1 + 2 * n by omega,
      Nat.digits_add 2 (by omega) 1 n (by omega) (Or.inl one_ne_zero)]
  simp [add_comm]

private lemma s2_pos {n : ℕ} (hn : 0 < n) : 0 < s2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hmod : n % 2 = 0
    · have hhalf : 0 < n / 2 := by omega
      have heq : n = 2 * (n / 2) := by omega
      rw [heq, s2_two_mul]
      exact ih (n / 2) (by omega) hhalf
    · have heq : n = 2 * (n / 2) + 1 := by omega
      rw [heq, s2_two_mul_add_one]
      omega

private lemma s2_succ_le (n : ℕ) : s2 (n + 1) ≤ s2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hmod : n % 2 = 0
    · obtain ⟨q, rfl⟩ : ∃ q, n = 2 * q := ⟨n / 2, by omega⟩
      rw [s2_two_mul_add_one, s2_two_mul]
    · obtain ⟨q, rfl⟩ : ∃ q, n = 2 * q + 1 := ⟨n / 2, by omega⟩
      rw [show 2 * q + 1 + 1 = 2 * (q + 1) by omega, s2_two_mul, s2_two_mul_add_one]
      have := ih q (by omega)
      omega

private lemma s2_add_le (a b : ℕ) : s2 (a + b) ≤ s2 a + s2 b := by
  suffices ∀ s a b, a + b = s → s2 (a + b) ≤ s2 a + s2 b from this (a + b) a b rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro a b hab
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      simp [s2_zero]
    · by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0
      · obtain ⟨qa, rfl⟩ : ∃ qa, a = 2 * qa := ⟨a / 2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ qb, b = 2 * qb := ⟨b / 2, by omega⟩
        rw [show 2 * qa + 2 * qb = 2 * (qa + qb) by omega, s2_two_mul, s2_two_mul, s2_two_mul]
        exact ih (qa + qb) (by omega) qa qb rfl
      · obtain ⟨qa, rfl⟩ : ∃ qa, a = 2 * qa := ⟨a / 2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ qb, b = 2 * qb + 1 := ⟨b / 2, by omega⟩
        rw [show 2 * qa + (2 * qb + 1) = 2 * (qa + qb) + 1 by omega,
            s2_two_mul_add_one, s2_two_mul, s2_two_mul_add_one]
        have := ih (qa + qb) (by omega) qa qb rfl
        omega
      · obtain ⟨qa, rfl⟩ : ∃ qa, a = 2 * qa + 1 := ⟨a / 2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ qb, b = 2 * qb := ⟨b / 2, by omega⟩
        rw [show 2 * qa + 1 + 2 * qb = 2 * (qa + qb) + 1 by omega,
            s2_two_mul_add_one, s2_two_mul_add_one, s2_two_mul]
        have := ih (qa + qb) (by omega) qa qb rfl
        omega
      · obtain ⟨qa, rfl⟩ : ∃ qa, a = 2 * qa + 1 := ⟨a / 2, by omega⟩
        obtain ⟨qb, rfl⟩ : ∃ qb, b = 2 * qb + 1 := ⟨b / 2, by omega⟩
        rw [show 2 * qa + 1 + (2 * qb + 1) = 2 * (qa + qb + 1) by omega,
            s2_two_mul, s2_two_mul_add_one, s2_two_mul_add_one]
        have hle1 := s2_succ_le (qa + qb)
        have hle2 := ih (qa + qb) (by omega) qa qb rfl
        omega

private lemma s2_eq_one_iff (n : ℕ) : s2 n = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [s2_zero, zero_ne_one, false_iff, not_exists]
      intro k
      exact (pow_pos (by omega : 0 < 2) k).ne
    · by_cases hmod : n % 2 = 0
      · have heq : n = 2 * (n / 2) := by omega
        rw [heq, s2_two_mul, ih (n / 2) (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [hk, pow_succ']⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => omega
          | succ k =>
            rw [pow_succ'] at hk
            exact ⟨k, by omega⟩
      · have heq : n = 2 * (n / 2) + 1 := by omega
        rw [heq, s2_two_mul_add_one]
        constructor
        · intro h
          have h0 : n / 2 = 0 := by
            by_contra hne
            have := s2_pos (Nat.pos_of_ne_zero hne)
            omega
          exact ⟨0, by omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero =>
            have h0 : n / 2 = 0 := by omega
            simp [h0, s2_zero]
          | succ k =>
            rw [pow_succ'] at hk
            omega

private lemma two_le_s2_three_mul {n : ℕ} (hn : 0 < n) : 2 ≤ s2 (3 * n) := by
  have hpos : 0 < s2 (3 * n) := s2_pos (by omega)
  by_contra hlt
  have h1 : s2 (3 * n) = 1 := by omega
  obtain ⟨k, hk⟩ := (s2_eq_one_iff (3 * n)).mp h1
  have h3dvd : 3 ∣ 2 ^ k := ⟨n, hk.symm⟩
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
  omega

private lemma s2_three_mul_two_pow (k : ℕ) : s2 (3 * 2 ^ k) = 2 := by
  induction k with
  | zero =>
    rw [pow_zero, mul_one]
    decide
  | succ k ih =>
    rw [pow_succ', ← mul_assoc, mul_comm 3 2, mul_assoc, s2_two_mul, ih]

private lemma padicValNat_two_choose_3n (n : ℕ) :
    padicValNat 2 ((3 * n).choose n) + s2 (3 * n) = 2 * s2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n) (n := 3 * n) (by omega)
  simp only [Nat.reduceSub, one_mul, show 3 * n - n = 2 * n by omega] at h
  change padicValNat 2 ((3 * n).choose n) = s2 n + s2 (2 * n) - s2 (3 * n) at h
  rw [s2_two_mul] at h
  have hle : s2 (3 * n) ≤ 2 * s2 n := by
    have := s2_add_le (2 * n) n
    rw [s2_two_mul, show 2 * n + n = 3 * n by omega] at this
    omega
  omega

private lemma padicValNat_two_tNat (k : ℕ) :
    padicValNat 2 (tNat k) = 2 * s2 k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold tNat
  rw [padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne']
  have h1 := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := 3 * k) (n := 6 * k)
    (by omega)
  simp only [Nat.reduceSub, one_mul, show 6 * k - 3 * k = 3 * k by omega] at h1
  change padicValNat 2 ((6 * k).choose (3 * k)) = s2 (3 * k) + s2 (3 * k) - s2 (6 * k) at h1
  have hs6 : s2 (6 * k) = s2 (3 * k) := by
    rw [show 6 * k = 2 * (3 * k) by omega, s2_two_mul]
  rw [hs6] at h1
  have h2 := padicValNat_two_choose_3n k
  omega

private def submasks (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => s2 k + s2 (n - k) = s2 n)

private lemma card_submasks (n : ℕ) : (submasks n).card = 2 ^ s2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    · by_cases hmod : n % 2 = 0
      · set m := n / 2
        have hnm : n = 2 * m := by omega
        have himg : submasks n = (submasks m).image (2 * ·) := by
          ext k
          simp only [submasks, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
          constructor
          · rintro ⟨hk, hsum⟩
            have hk_even : k % 2 = 0 := by
              by_contra hodd
              obtain ⟨a, rfl⟩ : ∃ a, k = 2 * a + 1 := ⟨k / 2, by omega⟩
              set b := (n - (2 * a + 1)) / 2
              have hnk1 : n - (2 * a + 1) = 2 * b + 1 := by omega
              have hm_eq : m = (a + b) + 1 := by omega
              rw [hnk1, s2_two_mul_add_one, s2_two_mul_add_one, hnm, s2_two_mul, hm_eq] at hsum
              have hle1 := s2_succ_le (a + b)
              have hle2 := s2_add_le a b
              omega
            obtain ⟨a, rfl⟩ : ∃ a, k = 2 * a := ⟨k / 2, by omega⟩
            refine ⟨a, ⟨by omega, ?_⟩, rfl⟩
            rw [hnm, show 2 * m - 2 * a = 2 * (m - a) by omega,
                s2_two_mul, s2_two_mul, s2_two_mul] at hsum
            exact hsum
          · rintro ⟨a, ⟨ha, hsum⟩, rfl⟩
            refine ⟨by omega, ?_⟩
            rw [hnm, show 2 * m - 2 * a = 2 * (m - a) by omega,
                s2_two_mul, s2_two_mul, s2_two_mul]
            exact hsum
        rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega),
            ih m (by omega), hnm, s2_two_mul]
      · set m := n / 2
        have hnm : n = 2 * m + 1 := by omega
        have hdisj : Disjoint ((submasks m).image (2 * ·)) ((submasks m).image (fun a => 2 * a + 1)) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [Finset.mem_image] at hx1 hx2
          rcases hx1 with ⟨a, _, rfl⟩
          rcases hx2 with ⟨b, _, hab⟩
          omega
        have hunion : submasks n =
            (submasks m).image (2 * ·) ∪ (submasks m).image (fun a => 2 * a + 1) := by
          ext k
          simp only [submasks, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
            Finset.mem_image]
          constructor
          · rintro ⟨hk, hsum⟩
            by_cases hke : k % 2 = 0
            · left
              obtain ⟨a, rfl⟩ : ∃ a, k = 2 * a := ⟨k / 2, by omega⟩
              refine ⟨a, ⟨by omega, ?_⟩, rfl⟩
              rw [hnm, show 2 * m + 1 - 2 * a = 2 * (m - a) + 1 by omega,
                  s2_two_mul, s2_two_mul_add_one, s2_two_mul_add_one] at hsum
              omega
            · right
              obtain ⟨a, rfl⟩ : ∃ a, k = 2 * a + 1 := ⟨k / 2, by omega⟩
              refine ⟨a, ⟨by omega, ?_⟩, rfl⟩
              rw [hnm, show 2 * m + 1 - (2 * a + 1) = 2 * (m - a) by omega,
                  s2_two_mul_add_one, s2_two_mul, s2_two_mul_add_one] at hsum
              omega
          · rintro (⟨a, ⟨ha, hsum⟩, rfl⟩ | ⟨a, ⟨ha, hsum⟩, rfl⟩)
            · refine ⟨by omega, ?_⟩
              rw [hnm, show 2 * m + 1 - 2 * a = 2 * (m - a) + 1 by omega,
                  s2_two_mul, s2_two_mul_add_one, s2_two_mul_add_one]
              omega
            · refine ⟨by omega, ?_⟩
              rw [hnm, show 2 * m + 1 - (2 * a + 1) = 2 * (m - a) by omega,
                  s2_two_mul_add_one, s2_two_mul, s2_two_mul_add_one]
              omega
        rw [hunion, Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective _ (fun a b h => by omega),
            Finset.card_image_of_injective _ (fun a b h => by omega),
            ih m (by omega), hnm, s2_two_mul_add_one, pow_succ]
        ring

private lemma sNat_mod_four_aux {n : ℕ} (hn : 0 < n) :
    ∃ M : ℕ, sNat n = 2 ^ (2 * s2 n) * M ∧ M % 4 = (2 ^ s2 n) % 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := 2 * s2 n
  set P : ℕ → Prop := fun k => s2 k + s2 (n - k) = s2 n
  have hval_term : ∀ k, padicValNat 2 (tNat k * tNat (n - k)) = 2 * s2 k + 2 * s2 (n - k) := by
    intro k
    rw [padicValNat.mul (tNat_pos k).ne' (tNat_pos (n - k)).ne',
        padicValNat_two_tNat, padicValNat_two_tNat]
  have hdvd_e : ∀ k ∈ Finset.range (n + 1), 2 ^ e ∣ tNat k * tNat (n - k) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [padicValNat_dvd_iff_le (Nat.mul_pos (tNat_pos k) (tNat_pos (n - k))).ne', hval_term]
    have hle := s2_add_le k (n - k)
    rw [Nat.add_sub_of_le hkn] at hle
    omega
  have hdvd_e2 : ∀ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ P k),
      2 ^ e * 4 ∣ tNat k * tNat (n - k) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk.1)
    rw [show 2 ^ e * 4 = 2 ^ (e + 2) by ring,
        padicValNat_dvd_iff_le (Nat.mul_pos (tNat_pos k) (tNat_pos (n - k))).ne', hval_term]
    have hle := s2_add_le k (n - k)
    rw [Nat.add_sub_of_le hkn] at hle
    dsimp only [P] at hk
    omega
  have hnonSub_dvd : 2 ^ e * 4 ∣
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ P k), tNat k * tNat (n - k) :=
    Finset.dvd_sum hdvd_e2
  obtain ⟨c, hc⟩ := hnonSub_dvd
  set u : ℕ → ℕ := fun k => (tNat k * tNat (n - k)) / 2 ^ e
  have hsub_eq : ∑ k ∈ submasks n, tNat k * tNat (n - k) = 2 ^ e * ∑ k ∈ submasks n, u k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact (Nat.mul_div_cancel' (hdvd_e k (Finset.mem_of_mem_filter k hk))).symm
  have hsNat_eq : sNat n = 2 ^ e * ((∑ k ∈ submasks n, u k) + 4 * c) := by
    unfold sNat
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) P]
    change (∑ k ∈ submasks n, tNat k * tNat (n - k)) +
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ P k), tNat k * tNat (n - k)) = _
    rw [hsub_eq, hc]
    ring
  refine ⟨(∑ k ∈ submasks n, u k) + 4 * c, hsNat_eq, ?_⟩
  rw [show ((∑ k ∈ submasks n, u k) + 4 * c) % 4 = (∑ k ∈ submasks n, u k) % 4 by omega]
  have hu_odd : ∀ k ∈ submasks n, u k % 2 = 1 := by
    intro k hk
    have hP : s2 k + s2 (n - k) = s2 n := (Finset.mem_filter.mp hk).2
    have hve : padicValNat 2 (tNat k * tNat (n - k)) = e := by
      rw [hval_term]; omega
    have hnot : ¬ 2 ^ (e + 1) ∣ tNat k * tNat (n - k) := by
      rw [← hve]
      exact pow_succ_padicValNat_not_dvd (Nat.mul_pos (tNat_pos k) (tNat_pos (n - k))).ne'
    have hdiv_e := hdvd_e k (Finset.mem_of_mem_filter k hk)
    by_contra hne
    have h2u : 2 ∣ u k := Nat.dvd_of_mod_eq_zero (by omega)
    apply hnot
    rcases h2u with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have hmul := Nat.mul_div_cancel' hdiv_e
    rw [show (tNat k * tNat (n - k)) / 2 ^ e = u k from rfl, hw] at hmul
    rw [pow_succ]
    linarith
  have hu_symm : ∀ k ≤ n, u (n - k) = u k := by
    intro k hkn
    dsimp only [u]
    rw [Nat.sub_sub_self hkn, mul_comm]
  set half := (submasks n).filter (fun k => 2 * k < n)
  set upper := (submasks n).filter (fun k => n < 2 * k)
  have hno_mid : ∀ k ∈ submasks n, 2 * k ≠ n := by
    intro k hk heq
    have hP : s2 k + s2 (n - k) = s2 n := (Finset.mem_filter.mp hk).2
    have hnk : n - k = k := by omega
    rw [hnk, ← heq, s2_two_mul] at hP
    have hkpos : 0 < k := by omega
    have := s2_pos hkpos
    omega
  have hdisj_hu : Disjoint half upper := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [half, upper, Finset.mem_filter] at hk1 hk2
    omega
  have hunion_hu : submasks n = half ∪ upper := by
    ext k
    simp only [half, upper, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hk
      have hne := hno_mid k hk
      by_cases hlt : 2 * k < n
      · exact Or.inl ⟨hk, hlt⟩
      · exact Or.inr ⟨hk, by omega⟩
    · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
  have hupper_img : upper = half.image (fun k => n - k) := by
    ext k
    simp only [upper, half, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hk, hgt⟩
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_filter k hk))
      have hP : s2 k + s2 (n - k) = s2 n := (Finset.mem_filter.mp hk).2
      refine ⟨n - k, ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩,
        by omega⟩
      rw [Nat.sub_sub_self hkn, add_comm]
      exact hP
    · rintro ⟨j, ⟨hj, hlt⟩, rfl⟩
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_filter j hj))
      have hP : s2 j + s2 (n - j) = s2 n := (Finset.mem_filter.mp hj).2
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩
      rw [Nat.sub_sub_self hjn, add_comm]
      exact hP
  have hinj : Set.InjOn (fun k => n - k) half := by
    intro a ha b hb hab
    dsimp only at hab
    have han : a ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_filter a (Finset.mem_of_mem_filter a ha)))
    have hbn : b ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_filter b (Finset.mem_of_mem_filter b hb)))
    omega
  have hcard_upper : upper.card = half.card := by
    rw [hupper_img, Finset.card_image_of_injOn hinj]
  have hcard_half : 2 * half.card = 2 ^ s2 n := by
    have h1 := card_submasks n
    rw [hunion_hu, Finset.card_union_of_disjoint hdisj_hu, hcard_upper] at h1
    omega
  have hsum_upper : ∑ k ∈ upper, u k = ∑ k ∈ half, u k := by
    rw [hupper_img, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_filter k (Finset.mem_of_mem_filter k hk)))
    exact hu_symm k hkn
  have hsum_sub : ∑ k ∈ submasks n, u k = 2 * ∑ k ∈ half, u k := by
    rw [hunion_hu, Finset.sum_union hdisj_hu, hsum_upper]
    omega
  have hsum_half_mod : (∑ k ∈ half, u k) % 2 = half.card % 2 := by
    rw [Finset.sum_nat_mod]
    have hcongr : ∑ k ∈ half, u k % 2 = ∑ _k ∈ half, 1 :=
      Finset.sum_congr rfl fun k hk => hu_odd k (Finset.mem_of_mem_filter k hk)
    rw [hcongr, Finset.sum_const, smul_eq_mul, mul_one]
  rw [hsum_sub, ← hcard_half]
  omega

/--
Conjecture (ii): For any positive integer $n$, we have $a(n) \equiv 0 \pmod 8$,
and $a(n)/8$ is odd if and only if $n$ is a power of two.
- _Zhi-Wei Sun_, Apr 19 2011
-/
theorem conjecture_3 (n : ℕ) (hn : 0 < n) :
    ∃ m : ℤ, a n = 8 * m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := (2 * n - 1) * (3 * n).choose n
  have hDpos : 0 < D := denom_pos hn
  obtain ⟨q, hq⟩ := denom_dvd_sNat hn
  change sNat n = D * q at hq
  have hqpos : 0 < q := by
    have := sNat_pos n
    nlinarith
  have hD_val : padicValNat 2 D + s2 (3 * n) = 2 * s2 n := by
    dsimp only [D]
    rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne',
        padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 2 * n - 1 by omega), zero_add]
    exact padicValNat_two_choose_3n n
  have hS_val : padicValNat 2 (sNat n) = padicValNat 2 D + padicValNat 2 q := by
    rw [hq, padicValNat.mul hDpos.ne' hqpos.ne']
  obtain ⟨M, hM_eq, hM_mod⟩ := sNat_mod_four_aux hn
  have hMpos : 0 < M := by
    have := sNat_pos n
    have : 0 < 2 ^ (2 * s2 n) := pow_pos (by omega) _
    nlinarith
  have hS_val_M : padicValNat 2 (sNat n) = 2 * s2 n + padicValNat 2 M := by
    rw [hM_eq, padicValNat.mul (pow_pos (by omega) _).ne' hMpos.ne', padicValNat.prime_pow]
  have hval_q : (∃ k : ℕ, n = 2 ^ k) → padicValNat 2 q = 3 := by
    rintro ⟨k, rfl⟩
    have hs2_1 : s2 (2 ^ k) = 1 := (s2_eq_one_iff (2 ^ k)).mpr ⟨k, rfl⟩
    have hs2_3 : s2 (3 * 2 ^ k) = 2 := s2_three_mul_two_pow k
    rw [hs2_1, pow_one] at hM_mod
    have h2M : 2 ∣ M := Nat.dvd_of_mod_eq_zero (by omega)
    have h4M : ¬ 4 ∣ M := by
      intro h4
      have : M % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
      omega
    have hvM_ge : 1 ≤ padicValNat 2 M := one_le_padicValNat_of_dvd hMpos.ne' h2M
    have hvM_lt : padicValNat 2 M < 2 := by
      by_contra hge
      apply h4M
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat_dvd_iff_le hMpos.ne']
      omega
    have hvM : padicValNat 2 M = 1 := by omega
    omega
  have hval_q_not : (¬ ∃ k : ℕ, n = 2 ^ k) → 4 ≤ padicValNat 2 q := by
    intro hnot
    have hs2_pos : 0 < s2 n := s2_pos hn
    have hs2_ne1 : s2 n ≠ 1 := fun h1 => hnot ((s2_eq_one_iff n).mp h1)
    have hs2_ge2 : 2 ≤ s2 n := by omega
    have h4pow : 4 ∣ 2 ^ s2 n := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 hs2_ge2
    have h4M : 4 ∣ M := by
      have : (2 ^ s2 n) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4pow
      exact Nat.dvd_of_mod_eq_zero (by omega)
    have hvM_ge2 : 2 ≤ padicValNat 2 M := by
      rw [← padicValNat_dvd_iff_le hMpos.ne']
      simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using h4M
    have hs2_3_ge2 : 2 ≤ s2 (3 * n) := two_le_s2_three_mul hn
    omega
  have hq_ge3 : 3 ≤ padicValNat 2 q := by
    by_cases hpow : ∃ k : ℕ, n = 2 ^ k
    · have := hval_q hpow; omega
    · have := hval_q_not hpow; omega
  have h8q : 8 ∣ q := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat_dvd_iff_le hqpos.ne']
    exact hq_ge3
  obtain ⟨m, hm⟩ := h8q
  refine ⟨(m : ℤ), ?_, ?_⟩
  · have hd : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
    have han : a n = (q : ℚ) := by
      rw [a_eq_div_nat hn]
      change (sNat n : ℚ) / (D : ℚ) = (q : ℚ)
      rw [hq, Nat.cast_mul, mul_div_cancel_left₀ _ hd]
    rw [han, hm]
    push_cast
    ring
  · constructor
    · rintro ⟨t, ht⟩
      by_contra hnot
      have hge4 := hval_q_not hnot
      have h16q : 16 ∣ q := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat_dvd_iff_le hqpos.ne']
        exact hge4
      rw [hm] at h16q
      rcases h16q with ⟨u, hu⟩
      have : m = 2 * u := by omega
      omega
    · intro hpow
      have hv3 := hval_q hpow
      have hnot16 : ¬ 16 ∣ q := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat_dvd_iff_le hqpos.ne']
        omega
      have hnot2m : ¬ 2 ∣ m := by
        intro ⟨u, hu⟩
        apply hnot16
        exact ⟨u, by omega⟩
      exact ⟨(m / 2 : ℕ), by omega⟩

end OeisA189286
