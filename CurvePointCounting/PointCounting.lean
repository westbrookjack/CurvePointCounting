import CurvePointCounting.EulerCriterion
import Mathlib

open BigOperators

namespace CurvePointCounting

/-!
# Quadratic characters and point counting over finite fields

This file develops the basic theory of quadratic characters on the unit group of a finite field
of odd characteristic, proves existence and uniqueness of the quadratic character, and derives
a formula for counting affine points on curves of the form `y^2 = f(x)` over finite fields, yielding
the estimate `#{(x,y) : K × K | y^2 = f x} ≤  2#K`, where `f : K → K` is any function.

## Definitions

- `IsQuadraticCharacter`
- `quadChar`
- `CharToFun`
- `affinePointSet_f`

## Results

- `exists_unique_quadraticCharacter`
- `affinePointSet_f_count`
- `affinePointSet_bounds`

## Notes

The quadratic character is first defined on `Kˣ →* ℂˣ` and then extended to a function
`K → ℂ` with `CharToFun` by sending `0` to `0`.
-/

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

noncomputable local instance : Fintype Kˣ := Fintype.ofFinite Kˣ

/-- A quadratic character on `Kˣ` is a nontrivial multiplicative character of order `2`. -/
structure IsQuadraticCharacter (χ : Kˣ →* ℂˣ) : Prop where
  sq_eq_one : ∀ a, χ a ^ 2 = 1
  nontrivial : χ ≠ 1

section QuadraticCharacter

omit [DecidableEq K] in
/-- If `ringChar K ≠ 2`, then `Fintype.card K ≠ 2`. -/
lemma card_ne_two_of_ringChar_ne_two : ringChar K ≠ 2 → Fintype.card K ≠ 2 := by
  contrapose!
  intro hK
  rw [← @neg_one_eq_one_iff]
  have heltk: ∀ x : K, x = 0 ∨ x = 1 := by
    classical
    have h_univ : (Finset.univ : Finset K).card = 2 := by
      simpa using hK
    rcases Finset.card_eq_two.mp h_univ with ⟨a, b, hab, huniv⟩
    have h0mem : (0 : K) ∈ ({a, b} : Finset K) := by
      have : (0 : K) ∈ (Finset.univ : Finset K) := by simp
      simpa [huniv] using this
    have h1mem : (1 : K) ∈ ({a, b} : Finset K) := by
      have : (1 : K) ∈ (Finset.univ : Finset K) := by simp
      simpa [huniv] using this
    have h01 : ({a, b} : Finset K) = ({(0 : K), (1 : K)} : Finset K) := by
      rcases Finset.mem_insert.mp h0mem with h0 | h0
      · rcases Finset.mem_insert.mp h1mem with h1 | h1
        · exfalso
          symm at h1
          rw[h1] at h0
          norm_num at h0
        · simp only [Finset.mem_singleton] at h1
          rw[ ← h0, ← h1]
      · rcases Finset.mem_insert.mp h1mem with h1 | h1
        · simp only [Finset.mem_singleton] at h0
          rw[← h0, ← h1]
          exact Finset.pair_comm 1 0
        · exfalso
          simp only [Finset.mem_singleton] at h0
          simp only [Finset.mem_singleton] at h1
          rw[h0.symm] at h1
          norm_num at h1
    intro x
    have hxmem : x ∈ ({(0 : K), (1 : K)} : Finset K) := by
      have : x ∈ (Finset.univ : Finset K) := by simp
      simpa [huniv, h01] using this
    simpa using Finset.mem_insert.mp hxmem
  have : (-1 : K) ≠ (0 : K) := by
    norm_num
  have := heltk (-1)
  tauto

/-- This defines the Frobenius endomorphism on a field of characteristic `2`. It is used
to prove that every element of `K` is a square iff `K` has characteristic `2`. -/
noncomputable def frobRing (hchar : ringChar K = 2) : K →+* K where
    toFun := fun u => u ^ 2
    map_one' := by simp
    map_mul' := by
      intro x y
      simp [pow_two, mul_comm, mul_left_comm]
    map_zero' := by simp
    map_add' := by
      intro x y
      simp only [pow_two, mul_add, add_mul]
      rw[mul_comm y x, add_assoc]
      simp only [add_right_inj]
      rw[← add_assoc]
      simp only [add_eq_right]
      have : x*y + x*y = 2 * (x*y) := Eq.symm (two_mul (x * y))
      rw[this]
      have (c : K) : 2 * c = 0 := by
        rw[← neg_one_eq_one_iff] at hchar
        have : (2 : K) = 0 := by
          have : (2 : K) = 1 + 1 := by norm_num
          nth_rewrite 1 [← hchar] at this
          simp only [neg_add_cancel] at this
          exact this
        rw[this]
        simp only [zero_mul]
      exact this (x * y)

omit [Fintype K] [DecidableEq K] in
/-- The Frobenius endomorphism in characteristic `2` is injective. -/
lemma frobRing_is_injective (hchar : ringChar K = 2) : Function.Injective (frobRing hchar) := by
  apply (RingHom.injective_iff_ker_eq_bot (frobRing hchar)).mpr
  rw [@RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  simp only [map_eq_zero] at hx
  exact hx

omit [Fintype K] [DecidableEq K] in
/-- Since Frobenius is injective, on a finite field it is also surjective. -/
lemma frobRing_is_surjective [Finite K] (hchar : ringChar K = 2) :
    Function.Surjective (frobRing hchar) := by
  rw[← Finite.injective_iff_surjective]
  exact frobRing_is_injective hchar

omit [Fintype K] [DecidableEq K] in
/-- Every element of `K` is a square if and only if `K` has characteristic `2`. -/
lemma all_isSquare_iff_ringChar_eq_two [Finite K] : (∀ x : K, IsSquare x) ↔ ringChar K = 2 := by
  constructor
  · intro hc
    have hsurj : Function.Surjective (fun u : Kˣ => u ^ 2) := by
      intro u
      rcases hc (u : K) with ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        intro hyz
        have : ((u : K) = 0) := by
          rw [hy, hyz]
          simp
        exact u.ne_zero this
      refine ⟨Units.mk0 y hy0, ?_⟩
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
      rw[hy]
      exact pow_two y
    have hinj : Function.Injective (fun u : Kˣ => u ^ 2) := by
      exact Finite.injective_iff_surjective.mpr hsurj
    have hneg1not0: (-1 : K) ≠ 0 := by
      norm_num
    have : (fun u : Kˣ => u ^ 2) (Units.mk0 (-1) hneg1not0) = (fun u : Kˣ => u ^ 2) 1 := by
      simp only [one_pow]
      have hsquares_commute_w_promotion (b : K) (hb : b ≠ 0) (hb2 : b^2 ≠ 0) :
          (Units.mk0 b hb)^2 = Units.mk0 (b^2) hb2 := by
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
      have hneg1sqnot0: (-1 : K) ^2 ≠ 0 := by
        norm_num
      rw[hsquares_commute_w_promotion (-1 : K) hneg1not0 hneg1sqnot0]
      simp only [even_two, Even.neg_pow, one_pow, Units.mk0_one]
    apply hinj at this
    refine neg_one_eq_one_iff.mp ?_
    have h1promotes : 1 = (Units.mk0 (1 : K) (by norm_num)) := by
      norm_num
    rw[h1promotes] at this
    have downward_eq (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
        Units.mk0 a ha = Units.mk0 b hb → a = b := by
      intro h
      apply congrArg (fun u : Kˣ => (u : K)) h
    apply downward_eq (-1 : K) 1 hneg1not0 (by norm_num) this
  · intro hK x
    have : ∃ y : K, y^2 = x := by
      have : ∃ y : K, x = (frobRing hK) y := by
        have hsqrtexists := (frobRing_is_surjective hK) x
        rcases hsqrtexists with ⟨y, hy⟩
        use y
        rw[← hy]
      rcases this with ⟨y, hy⟩
      use y
      rw[hy]
      rfl
    rcases this with ⟨y, hy⟩
    use y
    rw[← hy]
    exact pow_two y

omit [Fintype K] [DecidableEq K] in
/-- Convert between being a square in `K` and being a square in `Kˣ`. -/
lemma isSquare_coe_unit_iff (x : Kˣ) : IsSquare (x : K) ↔ IsSquare x := by
  constructor
  · intro h
    rcases h with ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro hyz
      have : (x : K) = 0 := by
        rw [hy, hyz]
        simp
      exact x.ne_zero this
    use Units.mk0 y hy0
    apply Units.ext
    rw[hy]
    have hy20 : y * y ≠ 0 := by
      intro hy
      have : (y = 0) := (mul_eq_zero_iff_right hy0).mp hy
      tauto
    have : (Units.mk0 y hy0) * (Units.mk0 y hy0) = Units.mk0 (y * y) hy20 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_mk0, Units.mk0_mul]
    rw[this]
    exact Eq.symm (Units.val_mk0 hy20)
  · intro h
    rcases h with ⟨y, hy⟩
    use (y : K)
    rw[hy]
    exact Units.val_mul y y

omit [Fintype K] [DecidableEq K] in
/-- Convert between being a square in `K` and being a square in `Kˣ` for a nonzero element. -/
lemma isSquare_mk0_iff (y : K) (hy0 : y ≠ 0) :
    IsSquare y ↔ IsSquare (Units.mk0 y hy0) := by
  constructor
  · intro h
    rw[← isSquare_coe_unit_iff (Units.mk0 y hy0)]
    have : y = (Units.mk0 y hy0 : K) := Eq.symm (Units.val_mk0 hy0)
    rw[← this]
    exact h
  · intro h
    rw[← isSquare_coe_unit_iff (Units.mk0 y hy0)] at h
    have : y = (Units.mk0 y hy0 : K) := Eq.symm (Units.val_mk0 hy0)
    rw[← this] at h
    exact h

/-- If `x^2 = 1` and `x ≠ 1`, then `x = -1`. -/
lemma eq_neg_one_of_sq_eq_one_of_ne_one {K : Type*} [Field K] {x : K}
    (hx : x ^ 2 = 1) (_ : x ≠ 1) : x = -1 := by
  have h0 : (x - 1) * (x + 1) = 0 := by
    simp only [mul_add, mul_one, sub_mul, one_mul, ← pow_two, hx]
    norm_num
  have h0' : x - 1 = 0 ∨ x + 1 = 0 := by
    apply mul_eq_zero.mp h0
  rcases h0' with h0 | h1
  · grind
  · grind

/-- If `x ≠ 0` and `ringChar K ≠ 2`, then the square of `x ^ ((|K| - 1) / 2)` is `1`. -/
lemma eulerCriterion_sq_eq_one {K : Type*} [Field K] [Fintype K] {x : K} (hx0 : x ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ((x ^ ((Fintype.card K - 1) / 2)) ^ 2 = 1) := by
  have hx20 := pow_ne_zero 2 hx0
  have : (x ^ ((Fintype.card K - 1) / 2)) ^ 2 = (x ^ 2) ^ ((Fintype.card K - 1) / 2) := by
    simp only [← pow_mul]
    have : ((Fintype.card K - 1) / 2 * 2) = (2 * ((Fintype.card K - 1) / 2)) := by
      rw[mul_comm]
    rw[this]
  rw[this, ← EulerCriterion.euler_criterion (K := K) (x ^ 2) hx20 hchar]
  use x
  exact pow_two x

/-- The underlying function of the quadratic character. -/
noncomputable def quadCharFun {K : Type*} [Field K] (x : Kˣ) : ℂˣ := by
  classical
  exact if IsSquare x then 1 else (-1 : ℂˣ)

/-- The quadratic character `Kˣ →* ℂˣ`. -/
noncomputable def quadChar {K : Type*} [Field K] [Fintype K] : Kˣ →* ℂˣ where
  toFun := quadCharFun
  map_one' := by
    simp only [quadCharFun, IsSquare.one, ↓reduceIte]
  map_mul' := by
    intro x y
    simp only [quadCharFun]
    have hx0 : (x : K) ≠ 0 := Units.ne_zero x
    have hy0 : (y : K) ≠ 0 := Units.ne_zero y
    have hxy0 : (x * y : K) ≠ 0 := Units.ne_zero (x * y)
    split_ifs with h1 h2 h3 h4 h5 h6 h7
    · norm_num
    · exfalso
      by_cases hchar2 : (ringChar K = 2)
      · apply h3
        have := (all_isSquare_iff_ringChar_eq_two.mpr hchar2 y)
        rcases this with ⟨z, hz⟩
        have hzne0: z ≠ 0 := by
          intro h
          have : (y = (0 : K)) := by
            rw [hz, h]
            simp
          apply Units.ne_zero y
          tauto
        use Units.mk0 z hzne0
        have hz2ne0 : z^2 ≠ 0 := pow_ne_zero 2 hzne0
        have : (Units.mk0 z hzne0) * (Units.mk0 z hzne0) = Units.mk0 (z^2) hz2ne0 := by
          apply Units.ext
          simp[pow_two]
        rw[this]
        rw[← pow_two] at hz
        exact Units.val_inj.mp hz
      · rw[← isSquare_coe_unit_iff (x * y)] at h1
        simp only [Units.val_mul] at h1
        rw[← isSquare_coe_unit_iff x] at h2
        rw[← isSquare_coe_unit_iff y] at h3
        rw [EulerCriterion.euler_criterion (K := K) ((x * y) : K) hxy0 hchar2] at h1
        rw [EulerCriterion.euler_criterion (K := K) (x : K) hx0 hchar2] at h2
        rw[EulerCriterion.euler_criterion (K := K) (y : K) hy0 hchar2] at h3
        rw[mul_pow] at h1
        rw[h2] at h1
        simp only [one_mul] at h1
        apply h3
        exact h1
    · exfalso
      by_cases hchar2 : (ringChar K = 2)
      · apply h2
        have := (all_isSquare_iff_ringChar_eq_two.mpr hchar2 x)
        rcases this with ⟨z, hz⟩
        have hzne0: z ≠ 0 := by
          intro h
          have : (x = (0 : K)) := by
            rw [hz, h]
            simp
          apply Units.ne_zero x
          tauto
        use Units.mk0 z hzne0
        have hz2ne0 : z^2 ≠ 0 := pow_ne_zero 2 hzne0
        have : (Units.mk0 z hzne0) * (Units.mk0 z hzne0) = Units.mk0 (z^2) hz2ne0 := by
          apply Units.ext
          simp[pow_two]
        rw[this]
        rw[← pow_two] at hz
        exact Units.val_inj.mp hz
      · rw[← isSquare_coe_unit_iff (x * y)] at h1
        simp only [Units.val_mul] at h1
        rw[← isSquare_coe_unit_iff x] at h2
        rw[← isSquare_coe_unit_iff y] at h4
        rw [EulerCriterion.euler_criterion (K := K) ((x * y) : K) hxy0 hchar2] at h1
        rw [EulerCriterion.euler_criterion (K := K) (x : K) hx0 hchar2] at h2
        rw[EulerCriterion.euler_criterion (K := K) (y : K) hy0 hchar2] at h4
        rw[mul_pow] at h1
        rw[h4] at h1
        simp only [mul_one] at h1
        apply h2
        exact h1
    · norm_num
    · exfalso
      by_cases hchar2 : (ringChar K = 2)
      · apply h1
        have := (all_isSquare_iff_ringChar_eq_two.mpr hchar2 (x*y))
        rcases this with ⟨z, hz⟩
        have hzne0: z ≠ 0 := by
          intro h
          have : (x*y = (0 : K)) := by
            rw [hz, h]
            simp
          apply Units.ne_zero  (x*y)
          tauto
        use Units.mk0 z hzne0
        have hz2ne0 : z^2 ≠ 0 := pow_ne_zero 2 hzne0
        have : (Units.mk0 z hzne0) * (Units.mk0 z hzne0) = Units.mk0 (z^2) hz2ne0 := by
          apply Units.ext
          simp[pow_two]
        rw[this]
        rw[← pow_two] at hz
        exact Units.val_inj.mp hz
      · rw[← isSquare_coe_unit_iff (x * y)] at h1
        simp only [Units.val_mul] at h1
        rw[← isSquare_coe_unit_iff x] at h5
        rw[← isSquare_coe_unit_iff y] at h6
        rw [EulerCriterion.euler_criterion (K := K) ((x * y) : K) hxy0 hchar2] at h1
        rw [EulerCriterion.euler_criterion (K := K) (x : K) hx0 hchar2] at h5
        rw[EulerCriterion.euler_criterion (K := K) (y : K) hy0 hchar2] at h6
        rw[mul_pow] at h1
        rw[h5, h6] at h1
        simp only [one_mul] at h1
        tauto
    · norm_num
    · norm_num
    · exfalso
      by_cases hchar2 : (ringChar K = 2)
      · apply h1
        have := (all_isSquare_iff_ringChar_eq_two.mpr hchar2 (x*y))
        rcases this with ⟨z, hz⟩
        have hzne0: z ≠ 0 := by
          intro h
          have : (x*y = (0 : K)) := by
            rw [hz, h]
            simp
          apply Units.ne_zero  (x*y)
          tauto
        use Units.mk0 z hzne0
        have hz2ne0 : z^2 ≠ 0 := pow_ne_zero 2 hzne0
        have : (Units.mk0 z hzne0) * (Units.mk0 z hzne0) = Units.mk0 (z^2) hz2ne0 := by
          apply Units.ext
          simp[pow_two]
        rw[this]
        rw[← pow_two] at hz
        exact Units.val_inj.mp hz
      · rw[← isSquare_coe_unit_iff (x * y)] at h1
        simp only [Units.val_mul] at h1
        rw[← isSquare_coe_unit_iff x] at h5
        rw[← isSquare_coe_unit_iff y] at h7
        rw [EulerCriterion.euler_criterion (K := K) ((x * y) : K) hxy0 hchar2] at h1
        rw [EulerCriterion.euler_criterion (K := K) (x : K) hx0 hchar2] at h5
        rw[EulerCriterion.euler_criterion (K := K) (y : K) hy0 hchar2] at h7
        have hx := eq_neg_one_of_sq_eq_one_of_ne_one (eulerCriterion_sq_eq_one hx0 hchar2) h5
        have hy := eq_neg_one_of_sq_eq_one_of_ne_one (eulerCriterion_sq_eq_one hy0 hchar2) h7
        have hxy := eq_neg_one_of_sq_eq_one_of_ne_one (eulerCriterion_sq_eq_one hxy0 hchar2) h1
        rw[mul_pow, hx, hy] at hxy
        norm_num at hxy
        have := neg_one_eq_one_iff.mp (id (Eq.symm hxy))
        tauto

/-- `quadChar` is a quadratic character. -/
lemma quadChar_isQuadraticCharacter {K : Type*} [Field K] [Fintype K] (hchar : ringChar K ≠ 2) :
    IsQuadraticCharacter (@quadChar K _ _) := by
  constructor
  · intro a
    simp only [quadChar, MonoidHom.coe_mk, OneHom.coe_mk]
    rw[quadCharFun]
    simp only [ite_pow, one_pow, even_two, Even.neg_pow, ite_self]
  · intro h
    have : ∀ x : Kˣ, quadChar x = 1 := by
      rw[h]
      intro x
      exact MonoidHom.one_apply x
    simp only [quadChar, MonoidHom.coe_mk, OneHom.coe_mk, quadCharFun] at this
    have : ∀ x : Kˣ, IsSquare x := by
      intro x
      have := this x
      simpa only [ite_eq_left_iff, neg_units_ne_self, imp_false, not_not] using this
    have : ∀ x : K, IsSquare x := by
      intro x
      by_cases hx0 : x = 0
      · simp only [hx0, IsSquare.zero]
      · rw[isSquare_mk0_iff x hx0]
        exact this (Units.mk0 x hx0)
    apply (all_isSquare_iff_ringChar_eq_two.mp) at this
    tauto

omit [Fintype K] [DecidableEq K] in
/-- The values of any quadratic character lie in `{±1}`. -/
lemma quadraticCharacter_eq_one_or_eq_neg_one (χ : Kˣ →* ℂˣ)
    (hχ : IsQuadraticCharacter χ) (x : Kˣ) :
    χ x = 1 ∨ χ x = -1 := by
  have hsq : χ x ^ 2 = 1 := hχ.sq_eq_one x
  by_cases h : χ x = 1
  · left; exact h
  · right
    have hsqC : (χ x : ℂ)^2 = 1 := (mem_rootsOfUnity' 2 (χ x)).mp hsq
    have hχC : (χ x : ℂ) ≠ 1 := by
      by_contra hc
      have : χ x = 1 := by
        rw [@Units.ext_iff]
        exact hc
      tauto
    have hχxneg1 : (χ x : ℂ) = -1 := by
      exact eq_neg_one_of_sq_eq_one_of_ne_one hsqC hχC
    have hχxne0 : (χ x : ℂ) ≠ 0 := by
      rw[hχxneg1]
      norm_num
    have : Units.mk0 (χ x : ℂ) hχxne0 = χ x := Units.mk0_val (χ x) hχxne0
    have hneg1ne0 : (-1 : ℂ) ≠ 0 := by
      norm_num
    have hsimp : Units.mk0 (-1 : ℂ) hneg1ne0 = Units.mk0 (χ x : ℂ) hχxne0 :=
      Units.mk0.congr_simp (-1) (↑(χ x)) (id (Eq.symm hχxneg1)) hneg1ne0
    rw[← hsimp] at this
    symm
    have hneg1promotes : (-1 : ℂˣ) = (Units.mk0 (-1 : ℂ) hneg1ne0) := by
      exact Units.val_inj.mp rfl
    rwa[← hneg1promotes] at this

/-- The subgroup `{±1}` of `ℂˣ`. -/
def plusMinusOneSubgroup : Subgroup ℂˣ where
  carrier := { z : ℂˣ | z = 1 ∨ z = -1 }
  one_mem' := by
    left
    rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  inv_mem' := by
    intro z hz
    rcases hz with rfl | rfl <;> simp

/-- `{±1}` is finite. -/
noncomputable instance : Fintype plusMinusOneSubgroup where
  elems :=
    { ⟨(1 : ℂˣ), by simp [plusMinusOneSubgroup]⟩,
      ⟨(-1 : ℂˣ), by simp [plusMinusOneSubgroup]⟩ }
  complete := by
    intro z
    rcases z with ⟨z, hz⟩
    simp only [plusMinusOneSubgroup, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_setOf_eq] at hz
    rcases hz with rfl | rfl
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    · simp only [Finset.mem_insert, one_mem, Subtype.mk.injEq, neg_units_ne_self,
      Finset.mem_singleton, or_true]

/-- If `z^2 = 1` in `ℂ`, then `z = 1` or `z = -1`. -/
lemma eq_one_or_eq_neg_one_of_sq_eq_one (z : ℂ) (hz : z ^ 2 = 1) : z = 1 ∨ z = -1 := by
      have : z ^ 2 - 1 = 0 := by
        rw[hz]
        norm_num
      have : (z - 1) * (z + 1) = 0 := by
        simp only [mul_add, mul_one, sub_mul, one_mul, ← pow_two]
        norm_num
        exact this
      have : z - 1 = 0 ∨ z + 1 = 0 := mul_eq_zero.mp this
      rcases this with h1 | hneg1
      · left
        have : (z - 1) + 1 = 0 + 1 := by
          rw[h1]
        simpa only [sub_add_cancel, zero_add] using this
      · right
        have : (z + 1) - 1 = 0 - 1 := by
          rw[hneg1]
        simpa only [add_sub_cancel_right, zero_sub] using this

omit [Fintype K] [DecidableEq K] in
/-- The range of any quadratic character is contained in `{±1}`. -/
lemma quadraticCharacter_range_le_plusMinusOne {z : ℂˣ} (χ : Kˣ →* ℂˣ)
    (hχ : IsQuadraticCharacter χ) :
    z ∈ ↑χ.range → z ∈ plusMinusOneSubgroup := by
  intro hz
  simp only [plusMinusOneSubgroup]
  rcases hz with ⟨x, hx⟩
  rw[← hx]
  have hχxsq1 : χ x ^ 2 = 1 := hχ.sq_eq_one x
  have hχxsq1C : (χ x : ℂ) ^ 2 = 1 := (mem_rootsOfUnity' 2 (χ x)).mp hχxsq1
  apply eq_one_or_eq_neg_one_of_sq_eq_one (χ x) at hχxsq1C
  rcases hχxsq1C with h1 | hneg1
  · left
    have := Units.mk0.congr_simp (χ x : ℂ) (1 : ℂ) h1 (Units.ne_zero (χ x))
    simpa only [Units.mk0_val, Units.mk0_one] using this
  · right
    have := Units.mk0.congr_simp (χ x : ℂ) (-1 : ℂ) hneg1 (Units.ne_zero (χ x))
    have mk0_negone (h : -1 ≠ 0 := by norm_num) : Units.mk0 (-1 : ℂ) h = -1 := by
      ext
      simp only [Units.mk0]
      norm_num
    simpa only [Units.mk0_val, mk0_negone (by norm_num)] using this

omit [Fintype K] [DecidableEq K] in
/-- The range of any quadratic character is exactly `{±1}`. -/
lemma quadraticCharacter_range_eq_plusMinusOne (χ : Kˣ →* ℂˣ) (hχ : IsQuadraticCharacter χ) :
    χ.range = plusMinusOneSubgroup := by
  ext z
  constructor
  · exact quadraticCharacter_range_le_plusMinusOne χ hχ
  · intro hz
    rw[plusMinusOneSubgroup] at hz
    rcases hz with h1 | hneg1
    · use 1
      rw[h1]
      exact MonoidHom.map_one χ
    · rw[hneg1]
      have : χ ≠ 1 := hχ.nontrivial
      have : ∃ x : Kˣ, χ x ≠ 1 := by
        contrapose! this
        exact MonoidHom.ext_iff.mpr this
      rcases this with ⟨x, hx⟩
      have : χ x ∈ χ.range := by
        use x
      have : χ x ∈ plusMinusOneSubgroup := quadraticCharacter_range_le_plusMinusOne χ hχ this
      simp only [plusMinusOneSubgroup] at this
      rcases this with h1' | hneg1'
      · tauto
      · rw[← hneg1']
        exact SetLike.mem_coe.mpr this

/-- If two group homomorphisms have the same kernel and the same range, then they differ by
an automorphism of the range. -/
lemma exists_mulEquiv_range_of_same_ker_same_range
    {G H : Type*} [Group G] [Group H]
    (f g : G →* H)
    (hker : f.ker = g.ker)
    (hrange : f.range = g.range) :
    ∃ φ : f.range ≃* f.range,
      ∀ x : G,
        ((φ (f.rangeRestrict x) : f.range) : H) = g x := by
  have hfg : ∀ {a b : G}, f a = f b → g a = g b := by
    intro a b hab
    have hkf : a⁻¹ * b ∈ f.ker := by
      simp [MonoidHom.mem_ker, hab]
    have hkg : a⁻¹ * b ∈ g.ker := by
      simpa [hker] using hkf
    simp only [MonoidHom.mem_ker, map_mul, map_inv] at hkg
    symm
    have : g a * ((g a)⁻¹ * g b) = g a := by
      rw[hkg]
      simp only [mul_one]
    rw[← mul_assoc] at this
    simpa only [mul_inv_cancel, one_mul] using this
  have hgf : ∀ {a b : G}, g a = g b → f a = f b := by
    intro a b hab
    have hkg : a⁻¹ * b ∈ g.ker := by
      simp [MonoidHom.mem_ker, hab]
    have hkf : a⁻¹ * b ∈ f.ker := by
      simpa [hker] using hkg
    simp only [MonoidHom.mem_ker, map_mul, map_inv] at hkf
    symm
    have : f a * ((f a)⁻¹ * f b) = f a := by
      rw[hkf]
      simp only [mul_one]
    rw[← mul_assoc] at this
    simpa only [mul_inv_cancel, one_mul] using this
  let wf : f.range → G := fun y => Classical.choose y.property
  have hwf : ∀ y : f.range, f (wf y) = y := by
    intro y
    exact Classical.choose_spec y.property
  let wg : f.range → G := fun y =>
    Classical.choose (show (y : H) ∈ g.range from by simpa [hrange] using y.property)
  have hwg : ∀ y : f.range, g (wg y) = y := by
    intro y
    exact Classical.choose_spec
      (show (y : H) ∈ g.range from by simpa [hrange] using y.property)
  let toFun : f.range → f.range := fun y =>
    ⟨g (wf y), by
      rw[hrange]
      exact ⟨wf y, rfl⟩⟩
  let invFun : f.range → f.range := fun y =>
    ⟨f (wg y), by
      exact ⟨wg y, rfl⟩⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro y
    apply Subtype.ext
    simp only [toFun, invFun]
    have hg_eq : g (wg (toFun y)) = g (wf y) := by
      simpa [toFun] using hwg (toFun y)
    have hf_eq : f (wg (toFun y)) = f (wf y) := hgf hg_eq
    simpa [hwf y] using hf_eq
  have hright : Function.RightInverse invFun toFun := by
    intro y
    apply Subtype.ext
    simp only [toFun, invFun]
    have hf_eq : f (wf (invFun y)) = f (wg y) := by
      simpa [invFun] using hwf (invFun y)
    have hg_eq : g (wf (invFun y)) = g (wg y) := hfg hf_eq
    simpa [hwg y] using hg_eq
  have hmul : ∀ y₁ y₂ : f.range, toFun (y₁ * y₂) = toFun y₁ * toFun y₂ := by
    intro y₁ y₂
    apply Subtype.ext
    have hf_eq : f (wf (y₁ * y₂)) = f (wf y₁ * wf y₂) := by
      rw [hwf (y₁ * y₂)]
      simp [map_mul, hwf y₁, hwf y₂]
    have hg_eq : g (wf (y₁ * y₂)) = g (wf y₁ * wf y₂) := hfg hf_eq
    simpa [toFun, map_mul] using hg_eq
  let φ : f.range ≃* f.range :=
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_mul' := hmul }
  use φ
  intro x
  let y : f.range := ⟨f x, ⟨x, rfl⟩⟩
  have hyφ : φ y = ⟨g x, by
      rw [hrange]
      exact ⟨x, rfl⟩⟩ := by
    apply Subtype.ext
    change g (wf y) = g x
    apply hfg
    simpa [y] using hwf y
  simpa [y, MonoidHom.rangeRestrict] using congrArg (fun z : f.range => ((z : f.range) : H)) hyφ

/-- If the automorphism group of the range is trivial, then group homomorphisms with the same kernel
and range are equal. -/
lemma eq_of_same_ker_same_range_of_rangeAut_trivial
    {G H : Type*} [Group G] [Group H]
    (f g : G →* H)
    (hker : f.ker = g.ker)
    (hrange : f.range = g.range)
    (hAut : ∀ φ : f.range ≃* f.range, φ = MulEquiv.refl _) :
    f = g := by
  rcases exists_mulEquiv_range_of_same_ker_same_range f g hker hrange with ⟨φ, hφ⟩
  have : φ = MulEquiv.refl _ := hAut φ
  rw[this] at hφ
  simp only [MulEquiv.refl_apply, MonoidHom.coe_rangeRestrict] at hφ
  ext x
  exact hφ x

omit [Fintype K] [DecidableEq K] in
/-- Any two quadratic characters with the same kernel are equal. -/
lemma quadraticCharacter_eq_of_same_ker (χ θ : Kˣ →* ℂˣ) (hχ : IsQuadraticCharacter χ)
    (hθ : IsQuadraticCharacter θ) (hker : χ.ker = θ.ker) : χ = θ := by
  apply eq_of_same_ker_same_range_of_rangeAut_trivial
  · exact hker
  · have hχrange : χ.range = plusMinusOneSubgroup := quadraticCharacter_range_eq_plusMinusOne χ hχ
    have hθrange : θ.range = plusMinusOneSubgroup := quadraticCharacter_range_eq_plusMinusOne θ hθ
    apply SetLike.ext'
    rw[hχrange, hθrange]
  · intro φ
    have hχrange : χ.range = plusMinusOneSubgroup := quadraticCharacter_range_eq_plusMinusOne χ hχ
    have : φ 1 = 1 := MulEquiv.map_one φ
    by_contra hc
    have : ∃ z : (χ.range), φ z ≠ z := by
      contrapose! hc
      exact MulEquiv.ext_iff.mpr hc
    rcases this with ⟨z, hz⟩
    have : (z : ℂˣ) ∈ plusMinusOneSubgroup := by
      rw[← hχrange]
      exact Subtype.coe_prop z
    rcases this with h1 | hneg1
    · have hzne1 : z ≠ 1 := by
        by_contra c
        rw[c] at hz
        tauto
      have hzne0 : ((z : ℂˣ) : ℂ) ≠ 0 := by
        rw[h1]
        norm_num
      have : Units.mk0 ((z : ℂˣ) : ℂ) hzne0 = (z : ℂˣ) := by
        exact Units.mk0_val (z : ℂˣ) hzne0
      rw[← this] at h1
      simp only [Units.mk0_val, OneMemClass.coe_eq_one] at h1
      tauto
    · have hminus_mem : -1 ∈ χ.range := by
        rw [hχrange]
        simp [plusMinusOneSubgroup]
      have hphi_ne_neg1 : ((φ z : χ.range) : ℂˣ) ≠ (-1 : ℂˣ) := by
        intro h
        apply hz
        ext
        simpa [hneg1] using h
      have hmem : ((φ z : χ.range) : ℂˣ) ∈ plusMinusOneSubgroup := by
        rw [← hχrange]
        exact (φ z).property
      have hcases : ((φ z : χ.range) : ℂˣ) = 1 ∨ ((φ z : χ.range) : ℂˣ) = -1 := by
        simpa [plusMinusOneSubgroup] using hmem
      have hphi_z_eq_1_ambient : ((φ z : χ.range) : ℂˣ) = 1 := by
        rcases hcases with h1 | hminus
        · exact h1
        · exfalso
          exact hphi_ne_neg1 hminus
      have hphi_z_eq_1 : φ z = 1 := by
        ext
        simpa using hphi_z_eq_1_ambient
      have hφinj : Function.Injective φ := MulEquiv.injective φ
      have : z = 1 := by
        apply hφinj
        rw[this, hphi_z_eq_1]
      rw[this] at hneg1
      norm_num at hneg1

omit [DecidableEq K] in
/-- The kernel of `quadChar` is contained in the kernel of any quadratic character. -/
lemma quadChar_ker_le_of_isQuadraticCharacter {χ : Kˣ →* ℂˣ} (hχ : IsQuadraticCharacter χ) :
    quadChar.ker ≤ χ.ker := by
  intro x hx
  simp only [quadChar, MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk, quadCharFun,
    ite_eq_left_iff, neg_units_ne_self, imp_false, not_not] at hx
  rcases hx with ⟨y, hy⟩
  rw[hy, ← pow_two]
  have hχysq1 : χ y ^ 2 = 1 := hχ.sq_eq_one y
  have : χ (y ^ 2) = (χ y) ^ 2 := MonoidHom.map_pow χ y 2
  rw[← this] at hχysq1
  exact MonoidHom.mem_ker.mpr hχysq1

omit [DecidableEq K] in
/-- Any two quadratic characters have kernels of the same cardinality. -/
lemma card_ker_eq_of_isQuadraticCharacter {χ θ : Kˣ →* ℂˣ}
    (hχ : IsQuadraticCharacter χ) (hθ : IsQuadraticCharacter θ) :
    Fintype.card χ.ker = Fintype.card θ.ker := by
  have hχrange : χ.range = plusMinusOneSubgroup := quadraticCharacter_range_eq_plusMinusOne χ hχ
  have hθrange : θ.range = plusMinusOneSubgroup :=
    quadraticCharacter_range_eq_plusMinusOne θ hθ
  have hχquot :
      Fintype.card (Kˣ ⧸ χ.ker) = Fintype.card plusMinusOneSubgroup := by
    have :=
      Fintype.card_congr ((QuotientGroup.quotientKerEquivRange χ).toEquiv)
    simpa [hχrange] using this
  have hθquot :
      Fintype.card (Kˣ ⧸ θ.ker) = Fintype.card plusMinusOneSubgroup := by
    have :=
      Fintype.card_congr ((QuotientGroup.quotientKerEquivRange θ).toEquiv)
    simpa [hθrange] using this
  have hquot :
      Fintype.card (Kˣ ⧸ χ.ker) = Fintype.card (Kˣ ⧸ θ.ker) := by
    rw [hχquot, hθquot]
  have hcardχ :
      Fintype.card Kˣ = Fintype.card χ.ker * Fintype.card (Kˣ ⧸ χ.ker) := by
    simpa [eq_comm, Subgroup.index_eq_card] using
      Subgroup.card_mul_index (χ.ker)
  have hcardθ :
      Fintype.card Kˣ = Fintype.card θ.ker * Fintype.card (Kˣ ⧸ θ.ker) := by
    simpa [eq_comm, Subgroup.index_eq_card] using
      Subgroup.card_mul_index (θ.ker)
  rw [hcardχ] at hcardθ
  rw [hquot] at hcardθ
  have : Fintype.card (Kˣ ⧸ θ.ker) > 0 := Fintype.card_pos
  apply Nat.mul_right_cancel this
  exact hcardθ

omit [DecidableEq K] in
/-- Any quadratic character has the same kernel as `quadChar`. -/
lemma ker_eq_quadChar_ker_of_isQuadraticCharacter {χ : Kˣ →* ℂˣ}
    (hχ : IsQuadraticCharacter χ) (hK : ringChar K ≠ 2) :
    χ.ker = quadChar.ker := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (quadChar_ker_le_of_isQuadraticCharacter hχ)
      have := (card_ker_eq_of_isQuadraticCharacter hχ (quadChar_isQuadraticCharacter hK)).symm
      simpa [Nat.card_eq_fintype_card] using le_of_eq this.symm

/-- Over a finite field of odd characteristic, there exists a unique quadratic character. -/
theorem exists_unique_quadraticCharacter
    {K : Type*} [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    ∃! χ : Kˣ →* ℂˣ, IsQuadraticCharacter χ := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have : Fintype.card K ≠ 2 := card_ne_two_of_ringChar_ne_two hK
  apply ExistsUnique.intro quadChar
  · exact quadChar_isQuadraticCharacter hK
  · intro χ hχ
    apply quadraticCharacter_eq_of_same_ker χ quadChar hχ (quadChar_isQuadraticCharacter hK)
    exact ker_eq_quadChar_ker_of_isQuadraticCharacter hχ hK

end QuadraticCharacter

section CurveCounting

variable (A B : K)

def is_on_curve_f (f : K → K) (x y : K) : Prop := (y ^ 2) = f x

/-- The set of all solutions to `y ^ 2 = f x` as a finite subset of `K × K`. -/
noncomputable def affinePointSet_f (f : K → K) : Finset (K × K) := by
  classical
  exact Finset.univ.filter (fun P : K × K => is_on_curve_f f P.1 P.2)

/-- Extend a quadratic character on `Kˣ` to a function `K → ℂ` by sending `0` to `0`. -/
noncomputable def CharToFun (χ : Kˣ →* ℂˣ) : K → ℂ := by
  classical
  exact fun x =>
    if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ)

/-- For `x : K`, the fiber of `y ^ 2 = f x` over `x`. -/
noncomputable def fiberOverX (f : K → K) (x : K) : Finset (K × K) :=
  (Finset.univ.filter fun y : K => y ^ 2 = f x).map
    ⟨fun y => (x, y), by
      intro a b h
      have := congrArg Prod.snd h
      simpa using this
    ⟩

/-- The solution set of `y ^ 2 = f x` is the union of the fibers over `x`. -/
lemma affinePointSet_f_eq_biUnion (f : K → K) :
    affinePointSet_f f = (Finset.univ : Finset K).biUnion (fiberOverX f) := by
  ext P
  constructor
  · intro h
    have hP : P.2 ^ 2 = f P.1 := by
      simp only [affinePointSet_f, is_on_curve_f, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      exact h
    have hmem : P ∈ fiberOverX f P.1 := by
      simp only [fiberOverX, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      use P.2
    apply Finset.mem_biUnion.mpr
    use P.1
    constructor
    · exact Finset.mem_univ P.1
    · exact hmem
  · intro h
    simp only [affinePointSet_f, is_on_curve_f, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h
    rcases h with ⟨x, hx⟩
    simp only [fiberOverX, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx
    rcases hx with ⟨y, hy⟩
    have h1 : P.1 = x := by
      have : P.1 = (x, y).1 := by rw [hy.2]
      simpa using this
    have h2 : P.2 = y := by
      have : P.2 = (x, y).2 := by rw [hy.2]
      simpa using this
    rw [h1, h2]
    exact hy.1

/-- Distinct fibers are disjoint. -/
lemma fiberOverX_disjoint {f : K → K} {x1 x2 : K} (h : x1 ≠ x2) :
    Disjoint (fiberOverX f x1) (fiberOverX f x2) := by
  rw [@Finset.disjoint_iff_ne]
  intro P1 hP1 P2 hP2 hEq
  have member_fiberOverX (P : K × K) (x : K) :
      P ∈ fiberOverX f x ↔ P.1 = x ∧ P.2 ^ 2 = f x := by
    constructor
    · intro hP
      simp only [fiberOverX, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk] at hP
      rcases hP with ⟨y, hy⟩
      constructor
      · have : P.1 = (x, y).1 := by rw [hy.2]
        simpa using this
      · have : P.2 = (x, y).2 := by rw [hy.2]
        rw [this]
        exact hy.1
    · intro hP
      simp only [fiberOverX, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      use P.2
      constructor
      · rw [hP.1] at hP
        exact hP.2
      · rw[← hP.1]
  have hP1' := (member_fiberOverX P1 x1).mp hP1
  have hP2' := (member_fiberOverX P2 x2).mp hP2
  have : P1.1 ≠ P2.1 := by
    rw [hP1'.1, hP2'.1]
    exact h
  exact this (by simp only [hEq])

/-- The cardinality of the solution set is the sum of the cardinalities of the fibers. -/
lemma card_affinePointSet_f_eq_sum_card_fiberOverX (f : K → K) :
    (affinePointSet_f f).card
      = ∑ x ∈ (Finset.univ : Finset K), (fiberOverX f x).card := by
  rw [affinePointSet_f_eq_biUnion (f := f)]
  apply Finset.card_biUnion
  intro x hx z hz hxz
  exact fiberOverX_disjoint (f := f) hxz

omit [DecidableEq K] in
/-- Helper lemma converting `Finset.card` to `Fintype.card` for `affinePointSet_f`. -/
lemma card_affinePointSet_f_eq_fintype_card (f : K → K) :
    (affinePointSet_f f).card = Fintype.card (affinePointSet_f f) := by
  simp

/-- Helper lemma converting `Finset.card` to `Fintype.card` for `fiberOverX`. -/
lemma card_fiberOverX_eq_fintype_card {x : K} (f : K → K) :
    (fiberOverX f x).card = Fintype.card (fiberOverX f x) := by
  simp

open Polynomial

/-- For `a : K`, the polynomial `X^2 - a`. -/
noncomputable def sq_roots_poly (a : K) : Polynomial K := (X : Polynomial K) ^ 2 - C a

omit [DecidableEq K] [Fintype K] in
/-- The polynomial `X^2 - a` is nonzero. -/
lemma sq_roots_poly_ne_zero (x : K) :
    sq_roots_poly x ≠ 0 := by
  simp only [sq_roots_poly, ne_eq]
  intro h
  have hcoeff := congrArg (fun p => coeff p 2) h
  simp at hcoeff

/-- If `x` is a nonzero square and `ringChar K ≠ 2`, then `x` has exactly two square roots. -/
lemma card_square_roots {x : K} (h0 : x ≠ 0) (hx : IsSquare x) (hK : ringChar K ≠ 2) :
    Fintype.card {z : K | z ^ 2 = x} = 2 := by
  rcases hx with ⟨y, hy⟩
  rw[← pow_two] at hy
  have sq_roots_subset : {y, -y} ⊆ {z : K | z ^ 2 = x} := by
    intro z hz
    rcases hz with rfl | rfl
    · rw[hy]
      exact Set.mem_setOf.mpr rfl
    · rw [hy]
      apply Set.mem_setOf.mpr
      norm_num
  have sq_roots_card : Fintype.card ({y, -y} : Set K) = 2 := by
    refine Set.card_insert {-y} ?_
    by_contra hymem
    simp only [Set.mem_singleton_iff] at hymem
    have : y⁻¹ * y = y⁻¹ * (-y) := by
      nth_rewrite 2 [hymem]
      norm_num
    simp only [mul_neg] at this
    apply hK
    rw [← @neg_one_eq_one_iff]
    have hy0 : y ≠ 0 := by
      by_contra hy0
      apply h0
      rw[hy0] at hy
      norm_num at hy
      exact hy
    rw[mul_comm, Field.mul_inv_cancel y hy0] at this
    exact this.symm
  have sq_roots_alt_def : {z : K | z ^ 2 = x} = (sq_roots_poly x).roots.toFinset := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_setOf_eq] at hz
      simp only [SetLike.mem_coe, Multiset.mem_toFinset,
        mem_roots', ne_eq, IsRoot.def, sq_roots_poly]
      constructor
      · exact sq_roots_poly_ne_zero x
      · simp only [eval_sub, eval_pow, eval_X, eval_C]
        rw[hz]
        norm_num
    · intro hz
      simp only [SetLike.mem_coe, Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def] at hz
      simp only [Set.mem_setOf_eq]
      have := hz.2
      simp[sq_roots_poly] at this
      grind
  have upper_bound_card : Fintype.card {z : K | z ^ 2 = x} ≤ 2 := by
    have hcard :
        Fintype.card ↑{z | z ^ 2 = x} = (sq_roots_poly x).roots.toFinset.card := by
      classical
      simp [sq_roots_alt_def]
      simpa using Fintype.card_coe ((sq_roots_poly x).roots.toFinset)
    have hroots :
        (sq_roots_poly x).roots.toFinset.card ≤ 2 := by
      have hdeg : (sq_roots_poly x).natDegree = 2 := by
        simp only [sq_roots_poly, natDegree_sub_C, natDegree_pow, natDegree_X, mul_one]
      rw[← hdeg]
      have ineq1 : (sq_roots_poly x).roots.card ≤ (sq_roots_poly x).natDegree :=
        card_roots' (sq_roots_poly x)
      have ineq2 : (sq_roots_poly x).roots.toFinset.card ≤ (sq_roots_poly x).roots.card :=
        Multiset.toFinset_card_le (sq_roots_poly x).roots
      exact Nat.le_trans ineq2 ineq1
    rwa[hcard]
  have hEq_finset :
    ({y, -y} : Finset K) = ({z | z ^ 2 = x}.toFinset) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have : z ∈ {z | z ^ 2 = x} := by
        apply sq_roots_subset
        simpa using hz
      exact Set.mem_toFinset.mpr this
    · have hpair :
          ({y, -y} : Finset K).card = Fintype.card ({y, -y} : Set K) := by
        classical
        have htoFinset : ({y, -y} : Set K).toFinset = ({y, -y} : Finset K) := by
          ext z
          simp
        rw [← htoFinset]
        have h := (Fintype.card_coe ((({y, -y} : Set K).toFinset))).symm
        simp only [Set.toFinset_insert, Set.toFinset_singleton, Finset.mem_insert,
          Finset.mem_singleton] at h
        simp only [Set.toFinset_insert, Set.toFinset_singleton, Fintype.card_ofFinset]
      rw [hpair, sq_roots_card]
      have hrootpair :
          ({z : K | z ^ 2 = x}.toFinset).card = Fintype.card {z : K | z ^ 2 = x} := by
        classical
        simpa using Set.toFinset_card ({z : K | z ^ 2 = x})
      rw [hrootpair]
      exact upper_bound_card
  have hpaircard : ({y, -y} : Finset K).card = 2 := by
    simpa using sq_roots_card
  have hrootcard : ({z : K | z ^ 2 = x}.toFinset).card = 2 := by
    rw [← hEq_finset]
    exact hpaircard
  rwa [← Set.toFinset_card ({z : K | z ^ 2 = x})]

/-- If `x` is not a square, then `x` has no square roots. -/
lemma card_square_roots_of_not_isSquare {x : K} (hx : ¬ IsSquare x) :
    Fintype.card {z : K | z ^ 2 = x} = 0 := by
  refine Fintype.card_eq_zero_iff.mpr ?_
  rw [@isEmpty_subtype]
  intro z hz
  apply hx
  use z
  rw[← pow_two]
  simp only [Set.mem_setOf_eq] at hz
  exact hz.symm

/-- A helper lemma converting a previous cardinality identity into the type needed later. -/
lemma card_affinePointSet_f_eq_sum_card_fiberOverX_finType (f : K → K) :
    Fintype.card (affinePointSet_f f)
      = ∑ x ∈ (Finset.univ : Finset K), Fintype.card (fiberOverX f x) := by
  simpa using card_affinePointSet_f_eq_sum_card_fiberOverX (f := f)

/-- The number of affine points on `y ^ 2 = f x` is given by a character sum. -/
theorem affinePointSet_f_count (f : K → K) (hK : ringChar K ≠ 2) :
    Fintype.card (affinePointSet_f f) =
    Fintype.card K + ∑ x ∈ (Finset.univ : Finset K), (CharToFun quadChar) (f x) := by
  have hsum :
    (Fintype.card K : ℂ) + ∑ x : K, CharToFun quadChar (f x)
      = ∑ x ∈ (Finset.univ : Finset K), (1 + CharToFun quadChar (f x)) := by
    have hsplit :
      ∑ x ∈ (Finset.univ : Finset K), (1 + CharToFun quadChar (f x))
        = (∑ x ∈ (Finset.univ : Finset K), (1 : ℂ))
          + (∑ x ∈ (Finset.univ : Finset K), CharToFun quadChar (f x)) := by
      exact Finset.sum_add_distrib
    rw [hsplit]
    have hone : ∑ x ∈ (Finset.univ : Finset K), (1 : ℂ) = Fintype.card K := by
      rw [← Finset.card_univ]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hone]
  rw [hsum, card_affinePointSet_f_eq_sum_card_fiberOverX_finType f]
  simp only [Fintype.card_coe, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp only [fiberOverX, Finset.card_map]
  by_cases hf0 : f x = 0
  · rw[hf0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, CharToFun,
      ↓reduceDIte, add_zero, Nat.cast_eq_one]
    refine (Fintype.existsUnique_iff_card_one fun x ↦ x = 0).mp ?_
    use 0
    constructor
    · simp only
    · intro y hy
      exact hy
  · have : CharToFun quadChar (f x) = quadChar (Units.mk0 (f x) hf0) := by
      simp only [CharToFun, hf0]
      exact dite_false
    rw[this]
    simp only [quadChar, MonoidHom.coe_mk, OneHom.coe_mk, quadCharFun]
    by_cases is_sq : IsSquare (f x)
    · have hsquare_units : IsSquare (Units.mk0 (f x) hf0) :=
        (isSquare_mk0_iff (f x) hf0).mp is_sq
      simp only [hsquare_units, ↓reduceIte, Units.val_one]
      norm_num
      have hsq : Fintype.card {z : K // z ^ 2 = f x} = 2 :=
        card_square_roots hf0 is_sq hK
      have hconv :
          ((({y : K | y ^ 2 = f x} : Set K).toFinset.card : ℂ))
            = Fintype.card {y : K // y ^ 2 = f x} := by
        simpa using
          (Set.toFinset_card ({y : K | y ^ 2 = f x} : Set K))
      have hsqC : (Fintype.card {z : K // z ^ 2 = f x} : ℂ) = 2 := by
        exact_mod_cast hsq
      simpa using hconv.trans hsqC
    · have hsquare_units : ¬ IsSquare (Units.mk0 (f x) hf0) := by
        intro hs
        have : IsSquare (f x) := (isSquare_mk0_iff (f x) hf0).mpr hs
        exact is_sq this
      simp only [hsquare_units, ↓reduceIte, Units.val_neg, Units.val_one, add_neg_cancel,
        Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
        forall_const]
      have hsq : Fintype.card {z : K // z ^ 2 = f x} = 0 :=
        card_square_roots_of_not_isSquare is_sq
      have hconv :
          ((({y : K | y ^ 2 = f x} : Set K).toFinset.card : ℂ))
            = Fintype.card {y : K // y ^ 2 = f x} := by
        simpa using
          (Set.toFinset_card ({y : K | y ^ 2 = f x} : Set K))
      have hsqC : (Fintype.card {z : K // z ^ 2 = f x} : ℂ) = 0 := by
        exact_mod_cast hsq
      intro z
      by_contra hc
      apply is_sq
      use z
      rw[pow_two] at hc
      symm
      exact hc

/-- The extended quadratic character with values in `ℤ`. -/
noncomputable def φ (a : K) : ℤ :=
  if a = 0 then 0
  else if IsSquare a then 1 else -1

/-- `φ`, viewed in `ℂ`, agrees with `CharToFun quadChar`. -/
lemma phi_eq_CharToFun_quadChar (a : K) :
    (φ a : ℂ) = CharToFun quadChar a := by
  simp [φ, CharToFun, quadChar, quadCharFun]
  by_cases ha0 : a = 0
  · simp[ha0]
  · by_cases ha_sq : IsSquare a
    · have : IsSquare (Units.mk0 a ha0) := (isSquare_mk0_iff a ha0).mp ha_sq
      simp[ha0, ha_sq, this]
    · have : ¬ IsSquare (Units.mk0 a ha0) := by
        intro hs
        have : IsSquare a := (isSquare_mk0_iff a ha0).mpr hs
        exact ha_sq this
      simp[ha0, ha_sq, this]

omit [DecidableEq K] in
/-- An upper bound on the number of affine points on `y ^ 2 = f x`. -/
theorem affinePointSet_bounds {f : K → K} (hK : ringChar K ≠ 2) :
    Fintype.card (affinePointSet_f f) ≤ 2 * Fintype.card K := by
  classical
  have hcount := affinePointSet_f_count f hK
  have sum_rw : ∀ x : K, CharToFun quadChar (f x) = (φ (f x) : ℂ) := by
    intro x
    simpa using (phi_eq_CharToFun_quadChar (f x)).symm
  simp only [Fintype.card_coe, sum_rw] at hcount
  have coerc_out :
      ((Fintype.card K : ℤ) : ℂ) + ∑ x, ((φ (f x) : ℤ) : ℂ) =
        (((Fintype.card K : ℤ) + ∑ x, φ (f x) : ℤ) : ℂ) := by
    simp only [Int.cast_add, Int.cast_sum]
  have hcount' :
      (Fintype.card (affinePointSet_f f) : ℂ) =
        (Fintype.card K : ℂ) + ∑ x : K, (φ (f x) : ℂ) := by
    simpa [phi_eq_CharToFun_quadChar] using hcount
  have hcount'' :
      (Fintype.card (affinePointSet_f f) : ℂ) =
        (((Fintype.card K : ℤ) + ∑ x : K, φ (f x)) : ℂ) := by
    calc
      (Fintype.card (affinePointSet_f f) : ℂ)
          = (Fintype.card K : ℂ) + ∑ x : K, (φ (f x) : ℂ) := hcount'
      _ = (((Fintype.card K : ℤ) + ∑ x : K, φ (f x)) : ℂ) := by
            simp only [Int.cast_natCast, Int.cast_sum]
  have hcountZ :
      (Fintype.card (affinePointSet_f f) : ℤ) =
        (Fintype.card K : ℤ) + ∑ x : K, φ (f x) := by
    exact_mod_cast hcount''
  have hphi_le_one : ∀ x : K, φ (f x) ≤ 1 := by
    intro x
    simp only [φ, Int.reduceNeg]
    by_cases hf0 : f x = 0
    · simp only [hf0, ↓reduceIte, zero_le_one]
    · by_cases hf_sq : IsSquare (f x)
      · simp only [hf0, ↓reduceIte, hf_sq, Std.le_refl]
      · simp only [hf0, ↓reduceIte, hf_sq, Int.reduceNeg, neg_le_self_iff, zero_le_one]
  have hsum_le :
      ∑ x : K, φ (f x) ≤ ∑ _x : K, (1 : ℤ) := by
    exact Finset.sum_le_sum (by
      intro x hx
      exact hphi_le_one x)
  have hones :
      (∑ _x : K, (1 : ℤ)) = Fintype.card K := by
    rw [← Finset.card_univ]
    simp
  have hboundZ :
      (Fintype.card (affinePointSet_f f) : ℤ) ≤ 2 * Fintype.card K := by
    rw [hcountZ]
    have hadd :
        (Fintype.card K : ℤ) + ∑ x : K, φ (f x)
          ≤ (Fintype.card K : ℤ) + ∑ _x : K, (1 : ℤ) := by
      exact Int.add_le_add_left hsum_le ↑(Fintype.card K)
    rw [hones] at hadd
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using hadd
  exact_mod_cast hboundZ

end CurveCounting

end CurvePointCounting
