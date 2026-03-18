import Mathlib
import Mathlib.Tactic.CancelDenoms.Core

open Polynomial

namespace EulerCriterion

/-!
## Euler's criterion over a finite field (via algebraic closures)

This file proves Euler's criterion for a finite field `K` of odd characteristic:
`IsSquare a ↔ a ^ ((card K - 1) / 2) = 1`.

A key intermediate step is to characterize the elements of the algebraic closure
satisfying `b ^ (card K) = b` as exactly the image of `K` under the canonical
embedding into `AlgebraicClosure K`.
-/

section Definitions

variable (K : Type*) [Field K] [Fintype K]

open Classical in
/-- `imgK_finset K` is the image of `K` inside `AlgebraicClosure K`, as a finset. -/
noncomputable def imgK_finset : Finset (AlgebraicClosure K) :=
  (Finset.univ : Finset K).image (algebraMap K (AlgebraicClosure K))

/--
`frob_poly K` is the polynomial `X^(card K) - X` over `AlgebraicClosure K`.
Its roots are exactly the elements `b` satisfying `b^(card K) = b`.
-/
noncomputable def frob_poly : Polynomial (AlgebraicClosure K) :=
  X ^ (Fintype.card K) - X

end Definitions

section AuxLemmas

variable (K : Type*) [Field K]

/--
If `char(K) ≠ 2` and `K` is finite, then `ringChar K` is congruent to `1 mod 2`.

This is used later to justify the identity `(q - 1) / 2 * 2 = q - 1` with `q = card K`.
-/
lemma odd_char_of_finite_field
    [Finite K] (hchar : ringChar K ≠ 2) :
    (ringChar K) % 2 = 1 := by
  have h : Nat.Prime (ringChar K) := by
    exact CharP.prime_ringChar K
  apply Nat.mod_two_not_eq_zero.mp
  by_contra hmod
  have cRingChar : ringChar K = 2 := by
    apply (Nat.Prime.even_iff h).mp
    exact Nat.even_iff.mpr hmod
  rw [cRingChar] at hchar
  tauto

/--
A simple cancellation lemma: if `a ≠ 0` and `a^n = a`, then `a^(n-1) = 1`.
-/
lemma power_eq_self
    (a : K) (n : ℕ) (ha : a ≠ 0) (han : a ^ n = a) :
    a ^ (n - 1) = 1 := by
  cases n with
  | zero =>
      simp only [pow_zero] at han
      rw[← han]
      norm_num
  | succ n =>
      simp only [Nat.succ_sub_one]
      rw [npow_add] at han
      simp only [pow_one] at han
      have hmul : a ^ n * a * a⁻¹ = a * a⁻¹ := by
        exact congrArg (fun z : K => z * a⁻¹) han
      rw [mul_assoc] at hmul
      have hinv : a * a⁻¹ = 1 := by
        exact CommGroupWithZero.mul_inv_cancel a ha
      rw [hinv] at hmul
      rw [mul_one] at hmul
      exact hmul

end AuxLemmas

section FrobeniusPolynomialFacts

variable (K : Type*) [Field K] [Fintype K]

/--
`X^(card K) - X` is not the zero polynomial over `AlgebraicClosure K`.
-/
lemma X_pow_card_sub_X_ne_zero :
    (X : Polynomial (AlgebraicClosure K)) ^ (Fintype.card K)
      - (X : Polynomial (AlgebraicClosure K)) ≠ 0 := by
  set q : ℕ := Fintype.card K
  have hq1 : q ≠ 1 := by
    have h1_lt_q : 1 < q := Fintype.one_lt_card
    exact ne_of_gt h1_lt_q
  intro h
  have hc :
      ((X : Polynomial (AlgebraicClosure K)) ^ q
            - (X : Polynomial (AlgebraicClosure K))).coeff q = 0 := by
    simp only [h, coeff_zero]
  have hc' :
      ((X : Polynomial (AlgebraicClosure K)) ^ q
            - (X : Polynomial (AlgebraicClosure K))).coeff q = 1 := by
    --The below line was given to me by the tactic simp?
    simp only [coeff_sub, coeff_X_pow, reduceIte, sub_eq_self, q]
    exact coeff_X_of_ne_one hq1
  rw [hc'] at hc
  norm_num at hc

/-- Degree computation: `natDegree (X^q - X) = q` for `q = Fintype.card K`. -/
lemma natDegree_frob_poly_eq :
    (frob_poly K).natDegree = Fintype.card K := by
  set q : ℕ := Fintype.card K
  have hcoeffq : (frob_poly K).coeff q = (1 : AlgebraicClosure K) := by
    have hq1 : q ≠ 1 := ne_of_gt (Fintype.one_lt_card : 1 < q)
    simp only [frob_poly, coeff_sub, coeff_X_pow, ↓reduceIte, sub_eq_self, q]
    exact coeff_X_of_ne_one hq1
  have hq_le : q ≤ (frob_poly K).natDegree := by
    have : (frob_poly K).coeff q ≠ (0 : AlgebraicClosure K) := by
      simp only [hcoeffq, ne_eq, one_ne_zero, not_false_eq_true]
    exact le_natDegree_of_ne_zero this
  have hle : (frob_poly K).natDegree ≤ q := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    have hm_ne1 : m ≠ 1 := by
      have : 1 < q := (Fintype.one_lt_card : 1 < q)
      exact by
        intro h1
        rw [h1] at hm
        have : q < q := Nat.lt_trans hm this
        norm_num at this
    --The below line was given to me by the tactic simp?
    simp only [frob_poly, coeff_sub, coeff_X_pow, hm.ne', ↓reduceIte, zero_sub, neg_eq_zero, q]
    exact coeff_X_of_ne_one hm_ne1
  exact le_antisymm (by simpa [q] using hle) (by simpa [q] using hq_le)

/-- Every element of the embedded copy of `K` is a root of `frob_poly K`. -/
lemma roots_of_frob_poly (a : K) :
    algebraMap K (AlgebraicClosure K) a ∈ (frob_poly K).roots := by
  simp only [frob_poly]
  rw [mem_roots]
  · simp only [IsRoot.def, eval_sub, eval_pow, eval_X]
    rw [← map_pow (algebraMap K (AlgebraicClosure K)), FiniteField.pow_card a]
    simp only [sub_self]
  · exact X_pow_card_sub_X_ne_zero K

/-- Cardinality of `imgK_finset K` is `card K` (injective image of `univ`). -/
lemma card_imgK_finset :
    (imgK_finset K).card = Fintype.card K := by
  classical
  have hinj : Function.Injective (algebraMap K (AlgebraicClosure K)) :=
    (algebraMap K (AlgebraicClosure K)).injective
  simpa [imgK_finset] using
    (Finset.card_image_of_injective Finset.univ hinj)


open Classical in
/--
`imgK_finset K` is contained in the finset of roots of `frob_poly K`.
This is the “obvious inclusion”: every element of the image is a root.
-/
lemma imgK_finset_subset_roots :
    imgK_finset K ⊆ (frob_poly K).roots.toFinset := by
  intro x hx
  rcases (by simpa [imgK_finset] using hx) with ⟨a, _, rfl⟩
  exact Multiset.mem_toFinset.mpr (roots_of_frob_poly K a)

open Classical in
/-- Lower bound on the number of roots via the inclusion `imgK_finset ⊆ roots`. -/
lemma card_roots_lower_bound :
    Fintype.card K ≤ (frob_poly K).roots.toFinset.card := by
  have hsubset := imgK_finset_subset_roots K
  have := Finset.card_le_card hsubset
  simpa [card_imgK_finset K] using this

open Classical in
/--
Upper bound on the number of distinct roots: `card (roots.toFinset) ≤ natDegree`.
-/
lemma card_roots_upper_bound :
    (frob_poly K).roots.toFinset.card ≤ (frob_poly K).natDegree := by
  have hf : frob_poly K ≠ 0 := by
    simpa [frob_poly] using X_pow_card_sub_X_ne_zero K
  have h1 : (frob_poly K).roots.toFinset.card ≤ (frob_poly K).roots.card :=
    Multiset.toFinset_card_le _
  have h2 : (frob_poly K).roots.card ≤ (frob_poly K).natDegree :=
    card_roots' (frob_poly K)
  exact le_trans h1 h2

open Classical in
/-- Combine the bounds to compute the cardinality of the roots finset. -/
lemma card_roots_frob_poly :
    (frob_poly K).roots.toFinset.card = Fintype.card K := by
  classical
  have hl := card_roots_lower_bound K
  have hu := card_roots_upper_bound K
  have hd := natDegree_frob_poly_eq K
  exact le_antisymm
    (by simpa [hd] using hu)
    hl

open Classical in
/--
Identify the finset of roots of `frob_poly K` with the image finset `imgK_finset K`.
-/
lemma roots_toFinset_eq_imgK_finset :
    (frob_poly K).roots.toFinset = imgK_finset K := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact imgK_finset_subset_roots K
  · rw [card_roots_frob_poly K, card_imgK_finset K]

/--
Characterize membership in the image of `K` inside `AlgebraicClosure K` by the Frobenius equation.
-/
theorem image_criterion (b : AlgebraicClosure K) :
    (∃ a : K, b = algebraMap K (AlgebraicClosure K) a) ↔ b ^ (Fintype.card K) = b := by
  classical
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    rw [ha]
    rw [← map_pow (algebraMap K (AlgebraicClosure K)) a (Fintype.card K)]
    rw [FiniteField.pow_card a]
  · intro h
    have : b ∈ (frob_poly K).roots := by
      simp only [frob_poly]
      rw [mem_roots]
      · simp only [IsRoot.def, eval_sub, eval_pow, eval_X]
        rw [h]
        norm_num
      · exact X_pow_card_sub_X_ne_zero K
    have : b ∈ imgK_finset K := by
      have : b ∈ (frob_poly K).roots.toFinset := Multiset.mem_toFinset.mpr this
      rwa [roots_toFinset_eq_imgK_finset K] at this
    rw [imgK_finset] at this
    rcases Finset.mem_image.mp this with ⟨c, _, rfl⟩
    use c

end FrobeniusPolynomialFacts

section EulerCriterionProof

variable (K : Type*) [Field K] [Fintype K]

/--
Forward direction used in Euler's criterion: if `a^((q-1)/2)=1` then `a` is a square.
-/
theorem forward_direction (hchar : ringChar K ≠ 2) (a : K) :
    a ^ ((Fintype.card K - 1) / 2) = 1 → ∃ b : K, a = b ^ 2 := by
  intro h
  let a' : AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K) a
  have : ∃ b : AlgebraicClosure K, a' = b * b := by
    exact IsAlgClosed.exists_eq_mul_self a'
  have ha' : a' ^ ((Fintype.card K - 1) / 2) = 1 := by
    simp only [a']
    rw [← map_pow (algebraMap K (AlgebraicClosure K)) a ((Fintype.card K - 1) / 2), h]
    exact algebraMap.coe_one
  rcases this with ⟨b, hb⟩
  rw [Eq.symm (pow_two b)] at hb
  rw [hb] at ha'
  have (m n : ℕ) : (b ^ m) ^ n = b ^ (m * n) := by
    exact Eq.symm (pow_mul b m n)
  rw [← pow_mul b 2 ((Fintype.card K - 1) / 2), mul_comm] at ha'
  have : ((Fintype.card K - 1) / 2) * 2 = Fintype.card K - 1 := by
    rw [← Nat.dvd_iff_div_mul_eq]
    have hcharconversion : CharP K (ringChar K) := ringChar.charP K
    have : ∃ n : ℕ+, Nat.Prime (ringChar K) ∧ Fintype.card K = (ringChar K) ^ (n : ℕ) :=
      FiniteField.card K (ringChar K)
    rcases this with ⟨n, _, hcard⟩
    rw [hcard]
    have hoddpow : (ringChar K) ^ (n : ℕ) % 2 = 1 := by
      rw [Nat.pow_mod]
      rw [odd_char_of_finite_field K hchar]
      norm_num
    have : ((ringChar K) ^ (n : ℕ) - 1) % 2 = 0 :=
      Nat.sub_mod_eq_zero_of_mod_eq hoddpow
    exact Nat.dvd_of_mod_eq_zero this
  rw [this] at ha'
  have hKcard_ne_zero : Fintype.card K ≠ 0 := by
    have : 0 < Fintype.card K := Fintype.card_pos
    exact ne_of_gt this
  have hb' : b ^ (Fintype.card K) = b := by
    have (n : ℕ) (hn : n ≠ 0) : b ^ n = b ^ (n - 1) * b :=
      Eq.symm (pow_sub_one_mul hn b)
    rw [this (Fintype.card K) hKcard_ne_zero, ha']
    norm_num
  rw [← image_criterion K b] at hb'
  rcases hb' with ⟨c, hc⟩
  use c
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [map_pow (algebraMap K (AlgebraicClosure K)) c 2, ← hc, ← hb]

/-- Euler's criterion over a finite field `K` of odd characteristic. -/
theorem euler_criterion
    (a : K) (ha : a ≠ 0) (hchar : ringChar K ≠ 2) :
    IsSquare a ↔ a ^ ((Fintype.card K - 1) / 2) = 1 := by
  constructor
  · intro h
    rcases h with ⟨b, hb⟩
    rw [← sq] at hb
    rw [hb]
    have hcharodd : (ringChar K) % 2 = 1 :=
      odd_char_of_finite_field K hchar
    have : (Fintype.card K - 1) / 2 * 2 = Fintype.card K - 1 := by
      rw [← Nat.dvd_iff_div_mul_eq]
      have hcharconversion : CharP K (ringChar K) := ringChar.charP K
      have : ∃ n : ℕ+, Nat.Prime (ringChar K) ∧ Fintype.card K = (ringChar K) ^ (n : ℕ) :=
        FiniteField.card K (ringChar K)
      rcases this with ⟨n, hprime, hcard⟩
      rw [hcard]
      have hoddpow : (ringChar K) ^ (n : ℕ) % 2 = 1 := by
        rw [Nat.pow_mod]
        rw [hcharodd]
        norm_num
      have : ((ringChar K) ^ (n : ℕ) - 1) % 2 = 0 :=
        Nat.sub_mod_eq_zero_of_mod_eq hoddpow
      exact Nat.dvd_of_mod_eq_zero this
    rw [Eq.symm (pow_mul' b ((Fintype.card K - 1) / 2) 2), this]
    have : b ^ (Fintype.card K) = b := FiniteField.pow_card b
    have hbnonzero : b ≠ 0 := by
      by_contra hzero
      rw [hzero] at hb
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hb
      tauto
    exact power_eq_self K b (Fintype.card K) hbnonzero this
  · intro h
    have := forward_direction K hchar a h
    rcases this with ⟨b, hb⟩
    use b
    rw [hb]
    exact pow_two b

end EulerCriterionProof

end EulerCriterion
