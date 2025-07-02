/-
Copyright (c) 2025 Jingyuan Li & Lin Zhou . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jingyuan Li & Lin Zhou
-/

import Mathlib.Analysis.Calculus.Deriv.Basic

open Set Function Real
open scoped Topology

set_option linter.unusedVariables false

/--
Calculates the Riemann-Stieltjes integral of a function `u` with respect to a distribution `Dist`
over the interval `[a, b]`, with a tolerance `ε` for approximation (Robust Riemann-Stieltjes Integral).

- `u`: The function to be integrated.
- `Dist`: The distribution function with respect to which the integral is computed.
- `a`, `b`: The endpoints of the interval `[a, b]`.
- `ε`: The tolerance for approximation when `u` is close to an indicator function.

Returns the computed integral value, adjusted for the tolerance if applicable.


--/
noncomputable def robustRiemannStieltjesIntegral (u : ℝ → ℝ) (Dist : ℝ → ℝ) (a b : ℝ) (ε : ℝ) : ℝ :=
  -- Check if u is exactly an indicator function 1_{(x₀, ∞)} for some x₀ ∈ (a, b)
  let P_exact : Prop := ∃ x₀ ∈ Ioo a b, ∀ x ∈ Icc a b, u x = if x > x₀ then 1 else 0

  -- Check if u is ε-close to an indicator function 1_{(x₀, ∞)} for some x₀ ∈ (a, b)
  let P_approx : Prop := ∃ x₀ ∈ Ioo a b, ∀ x ∈ Icc a b, |u x - (if x > x₀ then 1 else 0)| ≤ ε

  haveI : Decidable P_exact := Classical.propDecidable P_exact
  haveI : Decidable P_approx := Classical.propDecidable P_approx

  if h_exact : P_exact then
    -- Exact case: extract x₀ and return 1 - Dist x₀
    let x₀ := Classical.choose h_exact
    1 - Dist x₀
  else if h_approx : P_approx ∧ ε > 0 then
    -- Approximate case: extract x₀ and apply tolerance-adjusted computation
    let x₀ := Classical.choose h_approx.1
    -- Scale `ε` by `(b - a)` to account for the length of the interval `[a, b]`.
    -- This ensures that the tolerance is proportional to the size of the interval,
    -- making the adjustment meaningful regardless of the interval's length.
    let tolerance_adjustment := ε * (b - a)
    (1 - Dist x₀) + tolerance_adjustment
  else
    0 -- Fallback for functions that don't match either pattern


/-- If two indicator functions `1_{(x₁, ∞)}` and `1_{(x₂, ∞)}` are both ε-close to
function u on `Icc a b` with `x₁, x₂ ∈ Ioo a b`, then when ε is sufficiently small
relative to the separation |x₁ - x₂|, we have `x₁ = x₂`. This ensures the `x₀`
chosen in the tolerance-based integral definition is effectively unique for small ε.
Mathematically, this uniqueness is crucial for the well-definedness of the integral
approximation, as it guarantees consistency in the choice of the point `x₀` when
approximating functions close to an indicator function. -/
lemma uniqueness_of_indicator_x₀_tolerance {a b x₁ x₂ : ℝ} {u : ℝ → ℝ} {ε : ℝ}
    (hab : a < b) (hε_pos : ε > 0)
    (hx₁_mem : x₁ ∈ Ioo a b) (hx₂_mem : x₂ ∈ Ioo a b)
    (h_u_close_x₁ : ∀ x ∈ Icc a b, |u x - (if x > x₁ then (1 : ℝ) else (0 : ℝ))| ≤ ε)
    (h_u_close_x₂ : ∀ x ∈ Icc a b, |u x - (if x > x₂ then (1 : ℝ) else (0 : ℝ))| ≤ ε)
    (hε_small : ε < (1 : ℝ) / 2) :
    x₁ = x₂ := by
  -- Proof by contradiction: Assume x₁ ≠ x₂. This approach is used to demonstrate that the
  -- assumption of two distinct points x₁ and x₂ leads to a contradiction, thereby proving their uniqueness.
  by_contra h_neq
  -- `z` is the midpoint of `x₁` and `x₂`
  have h_lt_or_gt : x₁ < x₂ ∨ x₂ < x₁ := Ne.lt_or_lt h_neq
  rcases h_lt_or_gt with h_lt | h_gt
  -- Case 1: x₁ < x₂
  · let z := (x₁ + x₂) / 2
    have hz_mem_Ioo : z ∈ Ioo a b := by
      constructor
      · calc a < x₁ := hx₁_mem.1
           _ = (x₁ + x₁)/2 := by ring
           _ < (x₁ + x₂)/2 := by linarith [h_lt]
           _ = z := rfl
      · calc z = (x₁ + x₂)/2 := rfl
           _ < (x₂ + x₂)/2 := by linarith [h_lt]
           _ = x₂ := by ring
           _ < b := hx₂_mem.2
    have hz_mem_Icc : z ∈ Icc a b := Ioo_subset_Icc_self hz_mem_Ioo

    -- At point z: indicator for x₁ gives 1, indicator for x₂ gives 0
    have h_z_gt_x₁ : z > x₁ := by simp only [z]; linarith [h_lt]
    have h_z_lt_x₂ : z < x₂ := by simp only [z]; linarith [h_lt]
    have h_z_not_gt_x₂ : ¬(z > x₂) := not_lt.mpr (le_of_lt h_z_lt_x₂)
    -- Apply the triangle inequality to bound |1 - 0|: |1 - 0| ≤ |u z - 1| + |u z - 0|
    -- Use triangle inequality: |1 - 0| ≤ |u z - 1| + |u z - 0|
    have h_triangle : (1 : ℝ) ≤ |u z - 1| + |u z - 0| := by
      have h_eq : (1 : ℝ) = |(1 : ℝ) - (0 : ℝ)| := by norm_num
      rw [h_eq]
      have h_triangle_ineq : |(1 : ℝ) - (0 : ℝ)| ≤ |(1 : ℝ) - u z| + |u z - (0 : ℝ)| := by
        have h_rewrite : |(1 : ℝ) - (0 : ℝ)| = |(1 : ℝ) - u z + u z - (0 : ℝ)| := by ring_nf
        rw [h_rewrite]
        have h_add_form : (1 : ℝ) - u z + u z - (0 : ℝ) = (1 : ℝ) - u z + (u z - (0 : ℝ)) := by ring
        rw [h_add_form]
        exact abs_add_le ((1 : ℝ) - u z) (u z - (0 : ℝ))
      convert h_triangle_ineq using 1
      · simp [abs_sub_comm (1 : ℝ) (u z)]

    -- Apply the ε-closeness conditions
    have h_close_1 : |u z - 1| ≤ ε := by
      have h_cond : (if z > x₁ then (1 : ℝ) else (0 : ℝ)) = 1 := if_pos h_z_gt_x₁
      rw [← h_cond]
      exact h_u_close_x₁ z hz_mem_Icc
    have h_close_0 : |u z - 0| ≤ ε := by
      have h_cond : (if z > x₂ then (1 : ℝ) else (0 : ℝ)) = 0 := if_neg h_z_not_gt_x₂
      rw [← h_cond]
      exact h_u_close_x₂ z hz_mem_Icc

    -- Combine to get contradiction
    have : (1 : ℝ) ≤ ε + ε := by linarith [h_triangle, h_close_1, h_close_0]
    have : (1 : ℝ) ≤ 2 * ε := by linarith [this]
    have : (1 : ℝ) / 2 ≤ ε := by linarith [this, hε_pos]
    -- From the earlier steps, we derived that (1 : ℝ) ≤ 2 * ε, which implies (1 : ℝ) / 2 ≤ ε.
    -- This contradicts the assumption that ε < (1 : ℝ) / 2.
    linarith [this, hε_small] -- Contradiction with hε_small

  -- Case 2: x₂ < x₁ (symmetric argument)
  · let z := (x₁ + x₂) / 2
    have hz_mem_Ioo : z ∈ Ioo a b := by
      constructor
      · calc a < x₂ := hx₂_mem.1
           _ = (x₂ + x₂)/2 := by ring
           _ < (x₁ + x₂)/2 := by linarith [h_gt]
           _ = z := rfl
      · calc z = (x₁ + x₂)/2 := rfl
           _ < (x₁ + x₁)/2 := by linarith [h_gt]
           _ = x₁ := by ring
           _ < b := hx₁_mem.2
    have hz_mem_Icc : z ∈ Icc a b := Ioo_subset_Icc_self hz_mem_Ioo

    -- At point z: indicator for x₁ gives 0, indicator for x₂ gives 1
    have h_z_lt_x₁ : z < x₁ := by simp only [z]; linarith [h_gt]
    have h_z_gt_x₂ : z > x₂ := by simp only [z]; linarith [h_gt]
    have h_z_not_gt_x₁ : ¬(z > x₁) := not_lt.mpr (le_of_lt h_z_lt_x₁)

    -- Use triangle inequality: |0 - 1| ≤ |u z - 0| + |u z - 1|
    have h_triangle : (1 : ℝ) ≤ |u z - 0| + |u z - 1| := by
      have h_eq : (1 : ℝ) = |(0 : ℝ) - (1 : ℝ)| := by norm_num
      rw [h_eq]
      have h_triangle_ineq : |(0 : ℝ) - (1 : ℝ)| ≤ |(0 : ℝ) - u z| + |u z - (1 : ℝ)| := by
        have h_rewrite : |(0 : ℝ) - (1 : ℝ)| = |(0 : ℝ) - u z + u z - (1 : ℝ)| := by ring_nf
        rw [h_rewrite]
        have h_add_form : (0 : ℝ) - u z + u z - (1 : ℝ) = (0 : ℝ) - u z + (u z - (1 : ℝ)) := by ring
        rw [h_add_form]
        exact abs_add_le ((0 : ℝ) - u z) (u z - (1 : ℝ))
      convert h_triangle_ineq using 1
      · simp [abs_sub_comm (0 : ℝ) (u z)]

    -- Apply the ε-closeness conditions
    have h_close_0 : |u z - 0| ≤ ε := by
      have h_cond : (if z > x₁ then (1 : ℝ) else (0 : ℝ)) = 0 := if_neg h_z_not_gt_x₁
      rw [← h_cond]
      exact h_u_close_x₁ z hz_mem_Icc
    have h_close_1 : |u z - 1| ≤ ε := by
      have h_cond : (if z > x₂ then (1 : ℝ) else (0 : ℝ)) = 1 := if_pos h_z_gt_x₂
      rw [← h_cond]
      exact h_u_close_x₂ z hz_mem_Icc

    -- Combine to get contradiction
    have : (1 : ℝ) ≤ ε + ε := by linarith [h_triangle, h_close_0, h_close_1]
    have : (1 : ℝ) ≤ 2 * ε := by linarith [this]
    have : (1 : ℝ) / 2 ≤ ε := by linarith [this, hε_pos]
    linarith [this, hε_small] -- Contradiction with hε_small


/-- This lemma calculates the Robust Riemann-Stieltjes Integral for a function `u`
that is ε-close to an indicator function `1_{(x₀, ∞)}` over the interval `[a, b]`.
Assumptions:
- `a < b`: The interval `[a, b]` is non-degenerate.
- `u`: The function being integrated is ε-close to an indicator function.
- `Dist`: The distribution function with respect to which the integral is computed.
- `x₀ ∈ Ioo a b`: The point `x₀` is within the open interval `(a, b)`.
- `ε > 0`: The tolerance for approximation is positive.
- `ε < 1/2`: The tolerance is sufficiently small to ensure uniqueness of `x₀`.
- `u` is not exactly an indicator function.
The lemma ensures that the integral is computed using the tolerance-adjusted formula
`(1 - Dist x₀) + ε * (b - a)` when `u` is ε-close to an indicator function. -/
lemma integral_for_indicator_tolerance {a b : ℝ} (hab : a < b) {u : ℝ → ℝ} {Dist : ℝ → ℝ}
    {x₀ : ℝ} {ε : ℝ} (hε_pos : ε > 0) (hε_small : ε < 1/2)
    (hx₀_mem : x₀ ∈ Ioo a b)
    (h_u_close : ∀ x ∈ Icc a b, |u x - (if x > x₀ then (1 : ℝ) else (0 : ℝ))| ≤ ε)
    (h_not_exact : ¬(∃ x₀' ∈ Ioo a b, ∀ x ∈ Icc a b, u x = if x > x₀' then 1 else 0)) :
    robustRiemannStieltjesIntegral u Dist a b ε =
    (1 - Dist x₀) + ε * (b - a) := by
  -- Show that u satisfies the approximate property P_approx
  -- By the conditions of the lemma, `x₀` is unique when `u` is ε-close to an indicator function.
  have h_u_is_P_approx : ∃ x₀' ∈ Ioo a b, ∀ x ∈ Icc a b, |u x - (if x > x₀' then 1 else 0)| ≤ ε := by
    exact ⟨x₀, hx₀_mem, h_u_close⟩

  -- Unfold the definition
  dsimp [robustRiemannStieltjesIntegral]

  -- Since u is not exactly an indicator function
  rw [dif_neg h_not_exact]
  rw [dif_pos ⟨h_u_is_P_approx, hε_pos⟩]

  -- Show that Classical.choose h_u_is_P_approx = x₀ (under sufficient conditions)
  -- This requires the uniqueness lemma when ε < 1/2
  have h_x₀_eq : Classical.choose h_u_is_P_approx = x₀ := by
    let x₀' := Classical.choose h_u_is_P_approx
    have h_spec' : x₀' ∈ Ioo a b ∧ ∀ (x : ℝ), x ∈ Icc a b → |u x - (if x > x₀' then 1 else 0)| ≤ ε :=
      Classical.choose_spec h_u_is_P_approx
    exact uniqueness_of_indicator_x₀_tolerance hab hε_pos h_spec'.1 hx₀_mem h_spec'.2 h_u_close hε_small
  rw [h_x₀_eq]


/-- Flexible First-order stochastic dominance (FFSD) relation between two distributions F and G.
  F dominates G if F(x) ≤ G(x) + ε for all x in the interval [a, b].
  We also assume boundary conditions F(a)=G(a)=0 and F(b)=G(b)=1. -/
def Flexible_FSD (F G : ℝ → ℝ) (a b ε : ℝ) : Prop :=
  (∀ x ∈ Icc a b, F x ≤ G x + ε) ∧
  F a = 0 ∧
  G a = 0 ∧
  F b = 1 ∧
  G b = 1


theorem Flexible_FSD_iff_integral_indicator_ge (F G : ℝ → ℝ) (a b ε ε₁ ε₂ : ℝ)
  (hab : a < b) (hε_pos : ε > 0) (hε_small : ε < 1/2)
  (hε₁_pos : ε₁ > 0) (hε₁_small : ε₁ < 1/2)
  (hε₂_pos : ε₂ > 0) (hε₂_small : ε₂ < 1/2)
  (hFa : F a = 0) (hGa : G a = 0) (hFb : F b = 1) (hGb : G b = 1)
  (hε_eq : ε = (ε₁ - ε₂) * (b - a)) :
  Flexible_FSD F G a b ε ↔
  (∀ x₀ ∈ Ioo a b, ∀ u : ℝ → ℝ,
    (∀ x ∈ Icc a b, |u x - (if x > x₀ then (1 : ℝ) else (0 : ℝ))| ≤ ε₂) →
    (¬(∃ x₀' ∈ Ioo a b, ∀ x ∈ Icc a b, u x = if x > x₀' then 1 else 0)) →
    robustRiemannStieltjesIntegral u F a b ε₁ ≥
    robustRiemannStieltjesIntegral u G a b ε₂) := by
  constructor

  -- Forward direction (⇒): Assuming FFSD, prove integral inequality
  · intro h_tolerance_dominance
    intro x₀ hx₀_mem u h_u_close h_not_exact

    -- Extract components of tolerance FFSD
    have h_dom : ∀ x ∈ Icc a b, F x ≤ G x + ε := h_tolerance_dominance.1

    -- Since u is not exact, both integrals use the approximate case

    -- Prove ε₂ < ε₁ from hypotheses
    have h_eps2_lt_eps1 : ε₂ < ε₁ := by
      have hb_a_pos : b - a > 0 := sub_pos_of_lt hab
      -- From the hypothesis `hε_eq : ε = (ε₁ - ε₂) * (b - a)`, divide both sides by `(b - a)`
      -- (which is positive since `a < b`) to isolate `ε₁ - ε₂`.
      have h_e1_sub_e2_eq_eps_div_ba : ε₁ - ε₂ = ε / (b - a) :=
        (eq_div_iff hb_a_pos.ne').mpr (Eq.symm hε_eq)
      exact lt_of_sub_pos (h_e1_sub_e2_eq_eps_div_ba.symm ▸ div_pos hε_pos hb_a_pos)

    -- h_u_close is |u x - indicator x₀| ≤ ε₂ (due to theorem signature change)
    -- For F-integral, we need |u x - indicator x₀| ≤ ε₁
    have h_u_close_for_F : ∀ x ∈ Icc a b, |u x - (if x > x₀ then 1 else 0)| ≤ ε₁ :=
      fun x hx_icc => le_trans (h_u_close x hx_icc) (le_of_lt h_eps2_lt_eps1)

    have h_u_is_P_approx_F : ∃ x₀' ∈ Ioo a b, ∀ x ∈ Icc a b, |u x - (if x > x₀' then 1 else 0)| ≤ ε₁ := by
      exact ⟨x₀, hx₀_mem, h_u_close_for_F⟩

    have h_u_is_P_approx_G : ∃ x₀' ∈ Ioo a b, ∀ x ∈ Icc a b, |u x - (if x > x₀' then 1 else 0)| ≤ ε₂ := by
      exact ⟨x₀, hx₀_mem, h_u_close⟩ -- h_u_close is already |...| ≤ ε₂

    -- Calculate both integrals using the approximate formula
    have calc_int_F : robustRiemannStieltjesIntegral u F a b ε₁ = (1 - F x₀) + ε₁ * (b - a) := by
      apply integral_for_indicator_tolerance hab hε₁_pos hε₁_small hx₀_mem h_u_close_for_F h_not_exact

    have calc_int_G : robustRiemannStieltjesIntegral u G a b ε₂ = (1 - G x₀) + ε₂ * (b - a) := by
      apply integral_for_indicator_tolerance hab hε₂_pos hε₂_small hx₀_mem h_u_close h_not_exact

    -- Prove the inequality
    rw [calc_int_F, calc_int_G]
    -- Goal: (1 - F x₀) + ε₁ * (b - a) ≥ (1 - G x₀) + ε₂ * (b - a)
    -- This is equivalent to F x₀ ≤ G x₀ + (ε₁ - ε₂) * (b - a).
    -- By hε_eq, this is F x₀ ≤ G x₀ + ε.
    -- This is provable from h_dom.
    rw [ge_iff_le] -- Goal is now 1 - G x₀ + ε₂ * (b - a) ≤ 1 - F x₀ + ε₁ * (b - a)
    linarith [h_dom x₀ (Ioo_subset_Icc_self hx₀_mem), hε_eq]

  -- Backward direction (⇐): Assuming integral inequality, prove tolerance FSD
  · intro h_integral_indicator
    constructor
    · -- Prove ∀ x ∈ Icc a b, F x ≤ G x + ε
      intro x₀ hx₀_mem_Icc

      -- Handle boundary cases
      by_cases h_eq_a : x₀ = a
      · rw [h_eq_a, hFa, hGa]
        linarith [hε_pos]
      by_cases h_eq_b : x₀ = b
      · rw [h_eq_b, hFb, hGb]
        linarith [hε_pos]

      -- Interior case: x₀ ∈ Ioo a b
      push_neg at h_eq_a h_eq_b
      have hx₀_mem_Ioo : x₀ ∈ Ioo a b := ⟨lt_of_le_of_ne hx₀_mem_Icc.1 (Ne.symm h_eq_a), lt_of_le_of_ne hx₀_mem_Icc.2 h_eq_b⟩

      -- Define a perturbed indicator function `u` that is ε₂-close to the indicator function `1_{(x₀, ∞)}`.
      -- The perturbation ensures that `u` is not exactly an indicator function, while still satisfying the
      -- ε₂-closeness condition required by the theorem.
      let u := fun x => if x > x₀ then 1 - ε₂/2 else ε₂/2
      -- For simplicity, we'll use a perturbed indicator function
      let u := fun x => if x > x₀ then 1 - ε₂/2 else ε₂/2

      have h_u_satisfies_eps2_cond : ∀ x ∈ Icc a b, |u x - (if x > x₀ then (1 : ℝ) else (0 : ℝ))| ≤ ε₂ := by
        intro x _hx
        simp [u]
        by_cases h_gt : x > x₀
        · simp only [if_pos h_gt, u] -- Goal: |(1 - ε₂/2) - 1| ≤ ε₂ or similar
          simp only [sub_right_comm, sub_self, zero_sub, abs_neg, abs_of_nonneg (by linarith [hε₂_pos] : ε₂ / 2 ≥ 0)] -- Simplifies LHS to ε₂/2
          linarith [hε₂_pos]
        · simp only [if_neg h_gt, u, sub_zero] -- Goal: |ε₂/2| ≤ ε₂
          rw [abs_of_nonneg (show ε₂/2 ≥ 0 by linarith [hε₂_pos])] -- Goal: ε₂/2 ≤ ε₂
          linarith [hε₂_pos]

      have h_not_exact : ¬(∃ x₀' ∈ Ioo a b, ∀ x ∈ Icc a b, u x = if x > x₀' then 1 else 0) := by
        intro ⟨x₀_indicator, hx₀_indicator_mem, h_u_is_exact_indicator⟩
        -- u x is either ε₂/2 or 1 - ε₂/2.
        -- If u x were 0 or 1 (as per an exact indicator), this would lead to a contradiction
        -- with hε₂_pos (ε₂ > 0) or hε₂_small (ε₂ < 1/2).
        have h_u_a_val : u a = ε₂/2 := by
          simp [u, not_lt.mpr (le_of_lt hx₀_mem_Ioo.1)] -- a ≤ x₀ since a < x₀
        have h_indicator_val_at_a : (if a > x₀_indicator then (1 : ℝ) else 0) = 0 := by
          simp [not_lt.mpr (le_of_lt hx₀_indicator_mem.1)] -- a ≤ x₀_indicator since a < x₀_indicator
        specialize h_u_is_exact_indicator a (left_mem_Icc.mpr (le_of_lt hab))
        rw [h_indicator_val_at_a] at h_u_is_exact_indicator -- u a = 0
        rw [h_u_a_val] at h_u_is_exact_indicator -- ε₂/2 = 0
        linarith [hε₂_pos, h_u_is_exact_indicator]

      -- Apply hypothesis using the u that satisfies conditions with ε₂
      specialize h_integral_indicator x₀ hx₀_mem_Ioo u h_u_satisfies_eps2_cond h_not_exact

      -- Prepare h_u_close arguments for integral_for_indicator_tolerance calls
      have h_eps1_gt_eps2 : ε₁ > ε₂ := by
        have hb_a_pos : b - a > 0 := sub_pos_of_lt hab
        rw [hε_eq] at hε_pos -- After this, hε_pos is (ε₁ - ε₂) * (b - a) > 0
        exact lt_of_sub_pos ((mul_pos_iff_of_pos_right hb_a_pos).mp hε_pos)

      -- Lemma: |u x - indicator x₀| = ε₂/2 for the constructed u
      have h_u_abs_diff_eq_eps2_div_2 : ∀ x_val ∈ Icc a b, |u x_val - (if x_val > x₀ then 1 else 0)| = ε₂ / 2 := by
        intro x_val _hx_val_icc; simp only [u]
        by_cases hcond : x_val > x₀
        · simp only [if_pos hcond, sub_right_comm, sub_self, zero_sub, abs_neg]
          rw [abs_of_nonneg (by linarith [hε₂_pos] : ε₂ / 2 ≥ 0)]
        · simp only [if_neg hcond, sub_zero]
          rw [abs_of_nonneg (by linarith [hε₂_pos] : ε₂ / 2 ≥ 0)]

      have h_u_close_for_F : ∀ x ∈ Icc a b, |u x - (if x > x₀ then 1 else 0)| ≤ ε₁ := by
        intro x hx_icc; rw [h_u_abs_diff_eq_eps2_div_2 x hx_icc]
        linarith [h_eps1_gt_eps2, hε₂_pos] -- ε₂/2 ≤ ε₁ because ε₁ > ε₂ and ε₂ > 0 (so ε₂ ≥ ε₂/2)

      have h_u_close_for_G : ∀ x ∈ Icc a b, |u x - (if x > x₀ then 1 else 0)| ≤ ε₂ := by
        intro x hx_icc; rw [h_u_abs_diff_eq_eps2_div_2 x hx_icc]
        linarith [hε₂_pos] -- ε₂/2 ≤ ε₂ because ε₂ > 0

      -- Calculate integrals using approximate formula
      have calc_int_F : robustRiemannStieltjesIntegral u F a b ε₁ = (1 - F x₀) + ε₁ * (b - a) := by
        apply integral_for_indicator_tolerance hab hε₁_pos hε₁_small hx₀_mem_Ioo h_u_close_for_F h_not_exact

      have calc_int_G : robustRiemannStieltjesIntegral u G a b ε₂ = (1 - G x₀) + ε₂ * (b - a) := by
        apply integral_for_indicator_tolerance hab hε₂_pos hε₂_small hx₀_mem_Ioo h_u_close_for_G h_not_exact

      rw [calc_int_F, calc_int_G] at h_integral_indicator
      rw [ge_iff_le] at h_integral_indicator

      rw [hε_eq]
      linarith [h_integral_indicator]

    · -- Boundary conditions
      exact ⟨hFa, hGa, hFb, hGb⟩
