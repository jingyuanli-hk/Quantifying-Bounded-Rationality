/-
Copyright (c) 2025 Jingyuan Li & Lin Zhou . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jingyuan Li & Lin Zhou
Formalization of N-dimensional Flexible First-Order Stochastic Dominance
-/
import Mathlib.Analysis.Calculus.Deriv.Basic -- For basic analysis and real number properties
import Mathlib.Data.Finset.Powerset -- For Finset.powerset
import Mathlib.Data.Real.Basic -- For linarith etc.

open Set Function Real
open scoped Topology BigOperators -- For Π notation for products

set_option linter.unusedVariables false
set_option maxHeartbeats 400000 -- Increased for potentially complex proofs

/-!
# Flexible First-Order Stochastic Dominance in N Dimensions

This file formalizes a theorem relating flexible first-order stochastic dominance (FFSD)
in N dimensions to expected utility, specifically for functions
that are ε-close to indicator functions of upper-right orthants.

## Main definitions

* `RVector n`: N-dimensional vector of real numbers.
* `Icc_n a b`: N-dimensional closed rectangle.
* `Ioo_n a b`: N-dimensional open rectangle.
* `indicatorUpperRightOrthant`: Indicator function for the upper-right orthant.
* `survivalProbN`: N-dimensional survival probability.
* `Volume_n`: Volume of an N-dimensional rectangle.
* `robustRiemannStieltjesIntegralND`: Riemann-Stieltjes integral for N-dimensional case with tolerance.
* `Flexible_FSD_ND`: N-dimensional FFSD.

## Main results

* `uniqueness_of_indicatorUpperRightOrthant_x₀_tolerance_nd`: Uniqueness of the indicator function parameter `x₀`
  when a function `u` is ε-close to `indicatorUpperRightOrthant x₀`.
* `integral_for_indicatorUpperRightOrthant_tolerance_nd`: Calculates the integral for functions ε-close to
  upper-right orthant indicators.
* `Flexible_FSD_ND_iff_integral_indicatorUpperRightOrthant_ge`: Main theorem showing equivalence of
  flexible FSD (N-D) and expected utility for functions ε-close to indicator functions.
-/

/-- Type representing an N-dimensional vector of reals -/
def RVector (n : ℕ) := Fin n → ℝ

namespace RVector

variable {n : ℕ}

/-- Strict vector inequality: x < y if each component of x is less than
    the corresponding component of y -/
def lt (x y : RVector n) : Prop := ∀ i, x i < y i

/-- Vector inequality: x ≤ y if each component of x is less than or equal to
    the corresponding component of y -/
def le (x y : RVector n) : Prop := ∀ i, x i ≤ y i

instance : LT (RVector n) := ⟨lt⟩
instance : LE (RVector n) := ⟨le⟩

/-- All components greater: x > y if each component of x is greater than
    the corresponding component of y (used for orthant definitions) -/
def allGt (x y : RVector n) : Prop := ∀ i, x i > y i

/-- Create a mixed vector by selecting components from x₀ or b based on membership in set s -/
def mixedVector (x₀ b : RVector n) (s : Finset (Fin n)) : RVector n :=
  fun i => if i ∈ s then x₀ i else b i

end RVector

/-- Closed N-dimensional rectangle [a, b] -/
def Icc_n {n : ℕ} (a b : RVector n) : Set (RVector n) :=
  {x | RVector.le a x ∧ RVector.le x b}

/-- Open N-dimensional rectangle (a, b) -/
def Ioo_n {n : ℕ} (a b : RVector n) : Set (RVector n) :=
  {x | RVector.lt a x ∧ RVector.lt x b}

/-- Subset relation between rectangles -/
lemma Ioo_subset_Icc_self_n {n : ℕ} {a b : RVector n} :
    Ioo_n a b ⊆ Icc_n a b := by
  intro x hx
  constructor
  · intro i; exact le_of_lt (hx.1 i)
  · intro i; exact le_of_lt (hx.2 i)

/-- Indicator function for the upper-right orthant defined by `x₀`. -/
noncomputable def indicatorUpperRightOrthant {n : ℕ} (x₀ : RVector n) (x : RVector n) : ℝ :=
  haveI : Decidable (RVector.allGt x x₀) := Classical.propDecidable _
  if RVector.allGt x x₀ then 1 else 0

/-- Computes the survival probability in N dimensions.
    P(X₁>x₀₁,...,Xₙ>x₀ₙ)
-/
noncomputable def survivalProbN {n : ℕ} (Dist : RVector n → ℝ) (x₀ b : RVector n) : ℝ :=
  1 - ∑ s ∈ (Finset.powerset (Finset.univ : Finset (Fin n))) \ {∅},
    (-1) ^ (s.card + 1) * Dist (RVector.mixedVector x₀ b s)

/-- Volume of an N-dimensional rectangle [a, b] -/
noncomputable def Volume_n {n : ℕ} (a b : RVector n) : ℝ :=
  ∏ i ∈ Finset.univ, (b i - a i)

/-- Robust Riemann-Stieltjes Integral in N dimensions. -/
noncomputable def robustRiemannStieltjesIntegralND {n : ℕ} (u : RVector n → ℝ)
    (Dist : RVector n → ℝ) (a b : RVector n) (ε : ℝ)
    (hab_lt : ∀ i, a i < b i) -- Ensures Volume_n is positive
    : ℝ :=
  let P_exact : Prop := ∃ x₀_exact ∈ Ioo_n a b,
    ∀ x ∈ Icc_n a b, u x = indicatorUpperRightOrthant x₀_exact x
  let P_approx : Prop := ∃ x₀_approx ∈ Ioo_n a b,
    ∀ x ∈ Icc_n a b, |u x - indicatorUpperRightOrthant x₀_approx x| ≤ ε

  haveI : Decidable P_exact := Classical.propDecidable P_exact
  haveI : Decidable P_approx := Classical.propDecidable P_approx

  if h_exact : P_exact then
    let x₀_data := Classical.choose h_exact
    survivalProbN Dist x₀_data b
  else if h_approx_all : P_approx ∧ ε > 0 then
    let x₀_data := Classical.choose h_approx_all.1
    survivalProbN Dist x₀_data b + ε * Volume_n a b
  else
    0 -- Fallback

/-- Uniqueness of the reference point `x₀` for an indicator function approximation in N-D.
    If `u` is ε-close to `indicatorUpperRightOrthant x₁` and `indicatorUpperRightOrthant x₂`
    on `Icc_n a b`, and ε is small enough, then `x₁ = x₂`. -/
lemma uniqueness_of_indicatorUpperRightOrthant_x₀_tolerance_nd {n : ℕ} {a b x₁ x₂ : RVector n}
    (hab_lt : ∀ i, a i < b i) {u : RVector n → ℝ} {ε : ℝ} (hε_pos : ε > 0)
    (hx₁_mem : x₁ ∈ Ioo_n a b) (hx₂_mem : x₂ ∈ Ioo_n a b)
    (h_u_close_x₁ : ∀ x ∈ Icc_n a b, |u x - indicatorUpperRightOrthant x₁ x| ≤ ε)
    (h_u_close_x₂ : ∀ x ∈ Icc_n a b, |u x - indicatorUpperRightOrthant x₂ x| ≤ ε)
    (hε_small : ε < (1 : ℝ) / 2) :
    x₁ = x₂ := by
  by_contra h_neq
  have h_exists_diff : ∃ j, x₁ j ≠ x₂ j := by
    by_contra h_all_eq
    push_neg at h_all_eq
    exact h_neq (funext h_all_eq)

  rcases h_exists_diff with ⟨j, h_diff_at_j⟩
  have h_lt_or_gt : x₁ j < x₂ j ∨ x₂ j < x₁ j := Ne.lt_or_lt h_diff_at_j

  rcases h_lt_or_gt with h_x₁j_lt_x₂j | h_x₂j_lt_x₁j
  -- Case 1: x₁ j < x₂ j
  · let z_test_j_comp := (x₁ j + x₂ j) / 2
    let z_test : RVector n := fun i =>
      if i = j then z_test_j_comp else (max (x₁ i) (x₂ i) + b i) / 2

    have hz_test_mem_Ioo : z_test ∈ Ioo_n a b := by
      constructor
      · intro i
        dsimp [z_test, z_test_j_comp]
        by_cases h_eq_j : i = j
        · rw [h_eq_j, if_pos rfl]
          calc
            a j < x₁ j := hx₁_mem.1 j
            _ < (x₁ j + x₂ j) / 2 := by linarith [h_x₁j_lt_x₂j]
        · rw [if_neg h_eq_j]
          calc
            a i < x₁ i := hx₁_mem.1 i
            _ ≤ max (x₁ i) (x₂ i) := le_max_left _ _
            _ < (max (x₁ i) (x₂ i) + b i) / 2 := by
                have : max (x₁ i) (x₂ i) < b i := max_lt (hx₁_mem.2 i) (hx₂_mem.2 i)
                linarith [this]
      · intro i
        dsimp [z_test, z_test_j_comp]
        by_cases h_eq_j : i = j
        · rw [h_eq_j, if_pos rfl]
          calc
            (x₁ j + x₂ j) / 2 < x₂ j := by linarith [h_x₁j_lt_x₂j]
            _ < b j := hx₂_mem.2 j
        · rw [if_neg h_eq_j]
          calc
            (max (x₁ i) (x₂ i) + b i) / 2 < (b i + b i) / 2 := by
              apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
              apply add_lt_add_right
              exact max_lt (hx₁_mem.2 i) (hx₂_mem.2 i)
            _ = b i := by ring

    have hz_test_mem_Icc : z_test ∈ Icc_n a b := Ioo_subset_Icc_self_n hz_test_mem_Ioo

    have ind₁_val : indicatorUpperRightOrthant x₁ z_test = 1 := by
      unfold indicatorUpperRightOrthant; apply if_pos
      intro i; by_cases h_eq_j : i = j
      · subst h_eq_j
        dsimp only [z_test, z_test_j_comp] -- Exposes `if j = j then ...`
        rw [if_pos rfl] -- Simplifies the if condition
        linarith [h_x₁j_lt_x₂j]
      · dsimp [z_test, z_test_j_comp]; rw [if_neg h_eq_j]; calc
          x₁ i ≤ max (x₁ i) (x₂ i) := le_max_left _ _
          _ < (max (x₁ i) (x₂ i) + b i) / 2 := by linarith [max_lt (hx₁_mem.2 i) (hx₂_mem.2 i)]

    have ind₂_val : indicatorUpperRightOrthant x₂ z_test = 0 := by
      unfold indicatorUpperRightOrthant; apply if_neg
      intro h_all_gt
      specialize h_all_gt j
      dsimp [z_test, z_test_j_comp] at h_all_gt
      rw [if_pos rfl] at h_all_gt
      linarith [h_x₁j_lt_x₂j, h_all_gt]

    have h_u_close1 := h_u_close_x₁ z_test hz_test_mem_Icc
    have h_u_close2 := h_u_close_x₂ z_test hz_test_mem_Icc
    rw [ind₁_val] at h_u_close1 -- h_u_close1 is |u z_test - 1| ≤ ε
    rw [ind₂_val] at h_u_close2 -- h_u_close2 is |u z_test - 0| ≤ ε
    simp only [sub_zero] at h_u_close2 -- h_u_close2 is |u z_test| ≤ ε

    have h_one_eq_abs_diff : (1 : ℝ) = |(indicatorUpperRightOrthant x₁ z_test) - (indicatorUpperRightOrthant x₂ z_test)| := by
      rw [ind₁_val, ind₂_val, sub_zero, abs_one]

    have h_abs_diff_le_two_eps : |(indicatorUpperRightOrthant x₁ z_test) - (indicatorUpperRightOrthant x₂ z_test)| ≤ 2 * ε :=
      calc |(indicatorUpperRightOrthant x₁ z_test) - (indicatorUpperRightOrthant x₂ z_test)|
          = |(indicatorUpperRightOrthant x₁ z_test - u z_test) + (u z_test - indicatorUpperRightOrthant x₂ z_test)| := by simp only [sub_add_sub_cancel]
        _ ≤ |indicatorUpperRightOrthant x₁ z_test - u z_test| + |u z_test - indicatorUpperRightOrthant x₂ z_test| := abs_add _ _
        _ = |u z_test - indicatorUpperRightOrthant x₁ z_test| + |u z_test - indicatorUpperRightOrthant x₂ z_test| := by rw [abs_sub_comm (indicatorUpperRightOrthant x₁ z_test) (u z_test)]
        _ ≤ ε + ε := add_le_add (h_u_close_x₁ z_test hz_test_mem_Icc) (h_u_close_x₂ z_test hz_test_mem_Icc)
        _ = 2 * ε := by ring

    have h_one_le_two_eps : (1 : ℝ) ≤ 2 * ε := by
      rwa [← h_one_eq_abs_diff] at h_abs_diff_le_two_eps

    have h_half_le_eps : (1 : ℝ) / 2 ≤ ε := by linarith [h_one_le_two_eps] -- hε_pos not strictly needed for linarith here if 2 is known positive
    linarith [h_half_le_eps, hε_small]

  -- Case 2: x₂ j < x₁ j
  · let z_test_j_comp := (x₁ j + x₂ j) / 2
    let z_test : RVector n := fun i =>
      if i = j then z_test_j_comp else (max (x₁ i) (x₂ i) + b i) / 2
    have hz_test_mem_Ioo : z_test ∈ Ioo_n a b := by
      constructor
      · intro i
        dsimp [z_test, z_test_j_comp]
        by_cases h_eq_j : i = j
        · rw [h_eq_j, if_pos rfl]
          calc
            a j < x₂ j := hx₂_mem.1 j
            _ < (x₁ j + x₂ j) / 2 := by linarith [h_x₂j_lt_x₁j]
        · rw [if_neg h_eq_j]
          calc
            a i < x₂ i := hx₂_mem.1 i
            _ ≤ max (x₁ i) (x₂ i) := le_max_right _ _
            _ < (max (x₁ i) (x₂ i) + b i) / 2 := by
                have : max (x₁ i) (x₂ i) < b i := max_lt (hx₁_mem.2 i) (hx₂_mem.2 i)
                linarith [this]
      · intro i
        dsimp [z_test, z_test_j_comp]
        by_cases h_eq_j : i = j
        · rw [h_eq_j, if_pos rfl]
          calc
            (x₁ j + x₂ j) / 2 < x₁ j := by linarith [h_x₂j_lt_x₁j]
            _ < b j := hx₁_mem.2 j
        · rw [if_neg h_eq_j]
          calc
            (max (x₁ i) (x₂ i) + b i) / 2 < (b i + b i) / 2 := by
              apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
              apply add_lt_add_right
              exact max_lt (hx₁_mem.2 i) (hx₂_mem.2 i)
            _ = b i := by ring

    have hz_test_mem_Icc : z_test ∈ Icc_n a b := Ioo_subset_Icc_self_n hz_test_mem_Ioo

    have ind₁_val : indicatorUpperRightOrthant x₁ z_test = 0 := by
      unfold indicatorUpperRightOrthant; apply if_neg
      intro h_all_gt
      specialize h_all_gt j
      dsimp [z_test, z_test_j_comp] at h_all_gt
      rw [if_pos rfl] at h_all_gt
      linarith [h_x₂j_lt_x₁j, h_all_gt]

    have ind₂_val : indicatorUpperRightOrthant x₂ z_test = 1 := by
      unfold indicatorUpperRightOrthant; apply if_pos
      intro i; by_cases h_eq_j : i = j
      · subst h_eq_j; dsimp [z_test, z_test_j_comp]; rw [if_pos rfl]; linarith [h_x₂j_lt_x₁j]
      · dsimp [z_test, z_test_j_comp]; rw [if_neg h_eq_j]; calc
          x₂ i ≤ max (x₁ i) (x₂ i) := le_max_right _ _
          _ < (max (x₁ i) (x₂ i) + b i) / 2 := by linarith [max_lt (hx₁_mem.2 i) (hx₂_mem.2 i)]

    have h_u_close1 := h_u_close_x₁ z_test hz_test_mem_Icc
    have h_u_close2 := h_u_close_x₂ z_test hz_test_mem_Icc
    rw [ind₁_val] at h_u_close1 -- h_u_close1 is |u z_test - 0| ≤ ε
    rw [ind₂_val] at h_u_close2 -- h_u_close2 is |u z_test - 1| ≤ ε
    simp only [sub_zero] at h_u_close1 -- h_u_close1 is |u z_test| ≤ ε

    have h_one_eq_abs_diff : (1 : ℝ) = |(indicatorUpperRightOrthant x₂ z_test) - (indicatorUpperRightOrthant x₁ z_test)| := by
      rw [ind₂_val, ind₁_val, sub_zero, abs_one]

    have h_abs_diff_le_two_eps : |(indicatorUpperRightOrthant x₂ z_test) - (indicatorUpperRightOrthant x₁ z_test)| ≤ 2 * ε :=
      calc |(indicatorUpperRightOrthant x₂ z_test) - (indicatorUpperRightOrthant x₁ z_test)|
          = |(indicatorUpperRightOrthant x₂ z_test - u z_test) + (u z_test - indicatorUpperRightOrthant x₁ z_test)| := by simp only [sub_add_sub_cancel]
        _ ≤ |indicatorUpperRightOrthant x₂ z_test - u z_test| + |u z_test - indicatorUpperRightOrthant x₁ z_test| := abs_add _ _
        _ = |u z_test - indicatorUpperRightOrthant x₂ z_test| + |u z_test - indicatorUpperRightOrthant x₁ z_test| := by rw [abs_sub_comm (indicatorUpperRightOrthant x₂ z_test) (u z_test)]
        _ ≤ ε + ε := add_le_add (h_u_close_x₂ z_test hz_test_mem_Icc) (h_u_close_x₁ z_test hz_test_mem_Icc)
        _ = 2 * ε := by ring

    have h_one_le_two_eps : (1 : ℝ) ≤ 2 * ε := by
      rwa [← h_one_eq_abs_diff] at h_abs_diff_le_two_eps

    have h_half_le_eps : (1 : ℝ) / 2 ≤ ε := by linarith [h_one_le_two_eps] -- hε_pos not strictly needed for linarith here
    linarith [h_half_le_eps, hε_small]

/-- Computation of the robust integral for approximate orthant indicator functions -/
lemma integral_for_indicatorUpperRightOrthant_tolerance_nd {n : ℕ} {a b : RVector n}
    (hab_lt : ∀ i, a i < b i)
    {u : RVector n → ℝ} {Dist : RVector n → ℝ}
    {x₀_ref : RVector n} {ε : ℝ} (hε_pos : ε > 0) (hε_small : ε < 1/2)
    (hx₀_ref_mem : x₀_ref ∈ Ioo_n a b)
    (h_u_close_ref : ∀ x ∈ Icc_n a b, |u x - indicatorUpperRightOrthant x₀_ref x| ≤ ε)
    (h_not_exact : ¬(∃ x₀_exact ∈ Ioo_n a b, ∀ x ∈ Icc_n a b, u x = indicatorUpperRightOrthant x₀_exact x)) :
    robustRiemannStieltjesIntegralND u Dist a b ε hab_lt =
    survivalProbN Dist x₀_ref b + ε * Volume_n a b := by
  unfold robustRiemannStieltjesIntegralND
  rw [dif_neg h_not_exact]
  have h_P_approx_exists : ∃ x₀_approx ∈ Ioo_n a b,
    ∀ x ∈ Icc_n a b, |u x - indicatorUpperRightOrthant x₀_approx x| ≤ ε :=
    ⟨x₀_ref, hx₀_ref_mem, h_u_close_ref⟩
  rw [dif_pos ⟨h_P_approx_exists, hε_pos⟩]
  -- Prove that Classical.choose h_P_approx_exists must be x₀_ref
  let x₀_chosen := Classical.choose h_P_approx_exists -- x₀_chosen is the RVector n witness from h_P_approx_exists
  have h_chosen_spec := Classical.choose_spec h_P_approx_exists -- h_chosen_spec are the properties of x₀_chosen
  let h_x₀_chosen_mem := h_chosen_spec.1 -- Property 1: x₀_chosen ∈ Ioo_n a b
  let h_u_close_chosen := h_chosen_spec.2 -- Property 2: ∀ x ∈ Icc_n a b, |u x - indicatorUpperRightOrthant x₀_chosen x| ≤ ε
  have h_eq_x₀ : x₀_chosen = x₀_ref := by
    apply uniqueness_of_indicatorUpperRightOrthant_x₀_tolerance_nd hab_lt hε_pos
    exact h_x₀_chosen_mem -- Use property of x₀_chosen
    exact hx₀_ref_mem     -- Use property of x₀_ref
    exact h_u_close_chosen -- Use property of x₀_chosen
    exact h_u_close_ref    -- Use property of x₀_ref
    exact hε_small
  -- Unfold the let expression and use the fact that x₀_chosen = x₀_ref
  simp only []
  -- Now we need to show that Classical.choose h_P_approx_exists = x₀_ref
  conv_rhs => rw [← h_eq_x₀]



/-- N-dimensional Flexible First-Order Stochastic Dominance.
    F dominates G (with tolerance `ε_param_survival`) if for all `x₀` in the open rectangle,
    the survival probability for F at `x₀` is at least the survival probability for G at `x₀`
    minus `ε_param_survival`.
-/
def Flexible_FSD_ND {n : ℕ} (F G : RVector n → ℝ) (a b : RVector n) (ε_param_survival : ℝ) : Prop :=
  ∀ x₀ ∈ Ioo_n a b, survivalProbN F x₀ b ≥ survivalProbN G x₀ b - ε_param_survival



/-- Main theorem: N-dimensional Flexible FSD is equivalent to an expected utility inequality
    for all functions `u` that are `ε₂`-close to indicator functions of upper-right orthants. -/
theorem Flexible_FSD_ND_iff_integral_indicatorUpperRightOrthant_ge {n : ℕ}
    (F G : RVector n → ℝ) (a b : RVector n) (ε_param_survival ε₁ ε₂ : ℝ)
    (hab_lt : ∀ i, a i < b i)
    (hε₁_pos : ε₁ > 0) (hε₁_small : ε₁ < 1/2)
    (hε₂_pos : ε₂ > 0) (hε₂_small : ε₂ < 1/2)
    (h_vol_pos : Volume_n a b > 0) -- Ensured by hab_lt if n > 0. Explicit for n=0 or general case.
    (hε_eq : ε_param_survival = (ε₁ - ε₂) * Volume_n a b)
    (hε_param_nonneg : ε_param_survival ≥ 0)
    :
    Flexible_FSD_ND F G a b ε_param_survival ↔
    (∀ (x₀_param : RVector n) (hx₀_param : x₀_param ∈ Ioo_n a b) (u : RVector n → ℝ),
      (∀ x ∈ Icc_n a b, |u x - indicatorUpperRightOrthant x₀_param x| ≤ ε₂) →
      (¬(∃ x₀_exact ∈ Ioo_n a b, ∀ x ∈ Icc_n a b, u x = indicatorUpperRightOrthant x₀_exact x)) →
      robustRiemannStieltjesIntegralND u F a b ε₁ hab_lt ≥
      robustRiemannStieltjesIntegralND u G a b ε₂ hab_lt) := by
  constructor
  -- Forward direction (⇒)
  · intro h_tolerance_fsd
    intro x₀_param hx₀_param_mem u h_u_close_eps2 h_not_exact

    have h_eps1_ge_eps2 : ε₁ ≥ ε₂ := by
      have : ε₁ - ε₂ = ε_param_survival / Volume_n a b := by
        rw [hε_eq, mul_div_cancel_right₀ _ h_vol_pos.ne']
      rw [ge_iff_le, ← sub_nonneg]
      rw [this]
      exact div_nonneg hε_param_nonneg h_vol_pos.le

    have h_u_close_for_F : ∀ x ∈ Icc_n a b, |u x - indicatorUpperRightOrthant x₀_param x| ≤ ε₁ :=
      fun x hx_icc => le_trans (h_u_close_eps2 x hx_icc) h_eps1_ge_eps2

    have int_F_val : robustRiemannStieltjesIntegralND u F a b ε₁ hab_lt =
                      survivalProbN F x₀_param b + ε₁ * Volume_n a b :=
      integral_for_indicatorUpperRightOrthant_tolerance_nd hab_lt hε₁_pos hε₁_small hx₀_param_mem h_u_close_for_F h_not_exact

    have int_G_val : robustRiemannStieltjesIntegralND u G a b ε₂ hab_lt =
                      survivalProbN G x₀_param b + ε₂ * Volume_n a b :=
      integral_for_indicatorUpperRightOrthant_tolerance_nd hab_lt hε₂_pos hε₂_small hx₀_param_mem h_u_close_eps2 h_not_exact

    rw [int_F_val, int_G_val]
    specialize h_tolerance_fsd x₀_param hx₀_param_mem
    rw [ge_iff_le] -- Goal: survivalG + ε₂*Vol ≤ survivalF + ε₁*Vol
    -- h_tolerance_fsd: survivalProbN F x₀_param b ≥ survivalProbN G x₀_param b - ε_param_survival
    -- We need to show: survivalProbN G x₀_param b + ε₂ * Volume_n a b ≤ survivalProbN F x₀_param b + ε₁ * Volume_n a b
    -- From hε_eq: ε_param_survival = (ε₁ - ε₂) * Volume_n a b
    -- From h_tolerance_fsd: survivalProbN F x₀_param b ≥ survivalProbN G x₀_param b - (ε₁ - ε₂) * Volume_n a b
    have h_expanded : survivalProbN F x₀_param b ≥ survivalProbN G x₀_param b - (ε₁ - ε₂) * Volume_n a b := by
      rw [← hε_eq]
      exact h_tolerance_fsd
    linarith [h_expanded]

  -- Backward direction (⇐)
  · intro h_integral_ineq
    intro x₀_param hx₀_param_mem

    -- Define u to be ε₂/2 close to indicatorUpperRightOrthant x₀_param
    let u_pert := fun x : RVector n =>
      haveI : Decidable (RVector.allGt x x₀_param) := Classical.propDecidable _
      if RVector.allGt x x₀_param then (1 : ℝ) - ε₂ / 2 else ε₂ / 2

    have h_u_pert_close_eps2 : ∀ x ∈ Icc_n a b, |u_pert x - indicatorUpperRightOrthant x₀_param x| ≤ ε₂ := by
      intro x _hx_icc; simp only [u_pert, indicatorUpperRightOrthant]
      haveI : Decidable (RVector.allGt x x₀_param) := Classical.propDecidable _
      by_cases h_all_gt : RVector.allGt x x₀_param
      · simp only [if_pos h_all_gt, sub_right_comm, sub_self, zero_sub, abs_neg]
        rw [abs_of_nonneg (by linarith [hε₂_pos] : ε₂ / 2 ≥ 0)]
        linarith [hε₂_pos]
      · simp only [if_neg h_all_gt, sub_zero]
        rw [abs_of_nonneg (by linarith [hε₂_pos] : ε₂ / 2 ≥ 0)]
        linarith [hε₂_pos]

    have h_u_pert_not_exact : ¬(∃ x₀_exact ∈ Ioo_n a b, ∀ x ∈ Icc_n a b, u_pert x = indicatorUpperRightOrthant x₀_exact x) := by
      intro ⟨x₀_e, hx₀_e_mem, h_u_eq_ind⟩
      -- u_pert x is either ε₂/2 or 1 - ε₂/2. Indicator is 0 or 1.
      -- By construction, u_pert x is always either ε₂/2 or 1 - ε₂/2, both strictly between 0 and 1 because 0 < ε₂ < 1/2.
      -- Therefore, u_pert x can never be 0 or 1, so it cannot coincide with any indicator function.
      have h_u_pert_neq_0_1 : ∀ x, u_pert x ≠ 0 ∧ u_pert x ≠ 1 := by
        intro x; unfold u_pert
        have h_eps2_div_2_pos : ε₂ / 2 > 0 := div_pos hε₂_pos (by norm_num)
        have h_eps2_div_2_lt_1 : ε₂ / 2 < 1 := by linarith [hε₂_small] -- ε₂ < 1/2 ⇒ ε₂/2 < 1/4 < 1
        have h_1_minus_eps2_div_2_pos : 1 - ε₂ / 2 > 0 := by linarith [h_eps2_div_2_lt_1]
        have h_1_minus_eps2_div_2_lt_1 : 1 - ε₂ / 2 < 1 := by linarith [h_eps2_div_2_pos]
        by_cases h : RVector.allGt x x₀_param
        · rw [if_pos h]; exact ⟨ne_of_gt h_1_minus_eps2_div_2_pos, ne_of_lt h_1_minus_eps2_div_2_lt_1⟩
        · rw [if_neg h]; exact ⟨ne_of_gt h_eps2_div_2_pos, ne_of_lt h_eps2_div_2_lt_1⟩
      have hx₀_e_in_Icc : x₀_e ∈ Icc_n a b := Ioo_subset_Icc_self_n hx₀_e_mem
      specialize h_u_eq_ind x₀_e hx₀_e_in_Icc
      specialize h_u_pert_neq_0_1 x₀_e
      unfold indicatorUpperRightOrthant at h_u_eq_ind
      rw [h_u_eq_ind] at h_u_pert_neq_0_1
      by_cases h : RVector.allGt x₀_e x₀_e
      · rw [if_pos h] at h_u_pert_neq_0_1; exact h_u_pert_neq_0_1.2 rfl
      · rw [if_neg h] at h_u_pert_neq_0_1; exact h_u_pert_neq_0_1.1 rfl

    specialize h_integral_ineq x₀_param hx₀_param_mem u_pert h_u_pert_close_eps2 h_u_pert_not_exact

    have h_eps1_ge_eps2 : ε₁ ≥ ε₂ := by
      have : ε₁ - ε₂ = ε_param_survival / Volume_n a b := by
        rw [hε_eq, mul_div_cancel_right₀ _ h_vol_pos.ne']
      rw [ge_iff_le, ← sub_nonneg]
      rw [this]
      exact div_nonneg hε_param_nonneg h_vol_pos.le

    have h_u_pert_close_eps1 : ∀ x ∈ Icc_n a b, |u_pert x - indicatorUpperRightOrthant x₀_param x| ≤ ε₁ :=
      fun x hx_icc => le_trans (h_u_pert_close_eps2 x hx_icc) h_eps1_ge_eps2

    have int_F_val : robustRiemannStieltjesIntegralND u_pert F a b ε₁ hab_lt =
                      survivalProbN F x₀_param b + ε₁ * Volume_n a b :=
      integral_for_indicatorUpperRightOrthant_tolerance_nd hab_lt hε₁_pos hε₁_small hx₀_param_mem h_u_pert_close_eps1 h_u_pert_not_exact
    have int_G_val : robustRiemannStieltjesIntegralND u_pert G a b ε₂ hab_lt =
                      survivalProbN G x₀_param b + ε₂ * Volume_n a b :=
      integral_for_indicatorUpperRightOrthant_tolerance_nd hab_lt hε₂_pos hε₂_small hx₀_param_mem h_u_pert_close_eps2 h_u_pert_not_exact

    rw [int_F_val, int_G_val] at h_integral_ineq
    -- h_integral_ineq: survivalProbN F x₀_param b + ε₁ * Volume_n a b ≥ survivalProbN G x₀_param b + ε₂ * Volume_n a b
    -- We need to show: survivalProbN F x₀_param b ≥ survivalProbN G x₀_param b - ε_param_survival
    rw [hε_eq]
    -- After substitution: survivalProbN F x₀_param b ≥ survivalProbN G x₀_param b - (ε₁ - ε₂) * Volume_n a b
    -- This is exactly the definition of Flexible_FSD_ND F G a b ε_param_survival.
    linarith
