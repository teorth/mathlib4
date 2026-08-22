/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Compactly supported functions are dense in Schwartz space

This file proves that the compactly supported Schwartz functions are dense in `𝓢(E, F)`.
(Intended to eventually replace `W21_approximation` in the Wiener–Ikehara development.)

## Strategy

Fix a Schwartz function `f`. Let `χ : ContDiffBump (0 : E)` be a fixed bump equal to `1` on the
closed unit ball and supported in the ball of radius `2`. For `R > 0` set

  `bumpR R x = χ (R⁻¹ • x)`,

a smooth function equal to `1` on the ball of radius `R` and supported in the ball of radius `2R`.
Its `n`-th derivative scales like `R⁻ⁿ`: `‖Dⁿ (bumpR R)‖ ≤ R⁻ⁿ · ‖Dⁿ χ‖` (chain rule with the
linear map `x ↦ R⁻¹ • x`), and in finite dimensions `bumpR R` has *compact* support, hence
temperate growth.

Multiplication by `bumpR R` is therefore a continuous linear map on Schwartz space
(`SchwartzMap.smulLeftCLM`); we call its value at `f` the **truncation** `truncate f R`, which is
compactly supported. The claim is that `truncate f R → f` in the Schwartz topology as `R → ∞`.

By `schwartz_withSeminorms`, convergence in `𝓢(E, F)` is exactly convergence of every seminorm
`SchwartzMap.seminorm ℝ k n (truncate f R - f)` to `0`. Writing
`(truncate f R - f) x = (bumpR R x - 1) • f x` and expanding the `n`-th derivative by the Leibniz
rule (`norm_iteratedFDeriv_smul_le`):

* the difference `bumpR R - 1` and all its derivatives vanish on `‖x‖ ≤ R`, so only `‖x‖ > R`
  contributes;
* the `i = 0` term is `‖x‖ᵏ · |bumpR R x - 1| · ‖Dⁿ f x‖ ≤ ‖x‖ᵏ · ‖Dⁿ f x‖`, which is `≤ C / R`
  on `‖x‖ > R` because `‖x‖ᵏ⁺¹ ‖Dⁿ f‖` is bounded (Schwartz);
* each `i ≥ 1` term is `≤ ‖x‖ᵏ · (R⁻ⁱ Cᵢ) · ‖Dⁿ⁻ⁱ f x‖`, bounded by `R⁻ⁱ · (Schwartz seminorm)`.

Hence every seminorm of the difference is `O(R⁻¹) → 0`, giving `truncate f R → f`, and density
follows.

## Main statements

* `SchwartzMap.dense_hasCompactSupport`: the target — compactly supported Schwartz functions are
  dense.
* `SchwartzMap.tendsto_truncate`: the constructive engine — `truncate f R → f` as `R → ∞`.

-/

@[expose] public section

open scoped Topology ContDiff
open Filter Metric ContinuousLinearMap Real Finset Function

noncomputable section

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {R : ℝ} (f : 𝓢(E, F))

/-- A fixed reference bump on `E`: equal to `1` on the closed unit ball, supported in `ball 0 2`. -/
def bumpχ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The reference bump `bumpχ` as a plain function `E → ℝ`. -/
def χ₀ : E → ℝ := bumpχ (E := E)

/-- The reference bump rescaled by `R`: equal to `1` on `ball 0 R`, supported in `ball 0 (2R)`. -/
def bumpR (R : ℝ) (x : E) : ℝ := χ₀ (R⁻¹ • x)

section Bump

@[simp]
lemma bumpR_eq_one (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : bumpR R x = 1 := by
  refine bumpχ.one_of_mem_closedBall ?_
  grw [mem_closedBall_zero_iff, norm_smul, hx]
  simp [inv_mul_cancel₀ hR.ne', bumpχ, abs_of_pos hR]

lemma bumpR_nonneg (R : ℝ) (x : E) : 0 ≤ bumpR R x := bumpχ.nonneg' _

lemma bumpR_le_one (R : ℝ) (x : E) : bumpR R x ≤ 1 := bumpχ.le_one

lemma contDiff_bumpR (R : ℝ) : ContDiff ℝ ∞ (bumpR R (E := E)) :=
  bumpχ.contDiff.comp (contDiff_const_smul R⁻¹)

lemma support_χ₀ : support χ₀ = ball (0 : E) 2 := bumpχ.support_eq

lemma hasCompactSupport_χ₀ : HasCompactSupport (χ₀ : E → ℝ) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport _)
    (closure_minimal (support_χ₀.subset.trans ball_subset_closedBall) isClosed_closedBall)

/-- Each iterated derivative of the reference bump `χ₀` is bounded, uniformly over orders `≤ m`. -/
lemma exists_bound_iteratedFDeriv_χ₀ (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i ≤ m, ∀ y : E, ‖iteratedFDeriv ℝ i (χ₀ (E := E)) y‖ ≤ A := by
  have key (i) : ∃ A : ℝ, ∀ y : E, ‖iteratedFDeriv ℝ i χ₀ y‖ ≤ A :=
    (bumpχ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_χ₀.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y => ?_⟩
  exact (hA i y).trans (le_max_of_le_right (le_sup' A (by grind)))

lemma support_bumpR (hR : 0 < R) :
    support (bumpR R (E := E)) ⊆ closedBall (0 : E) (2 * R) := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  change R⁻¹ • x ∈ support χ₀ at hx
  simp [support_χ₀, norm_smul, abs_of_pos, inv_mul_lt_iff₀, hR] at hx
  linarith

lemma hasCompactSupport_bumpR (hR : 0 < R) : HasCompactSupport (bumpR R (E := E)) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall 0 (2 * R)) (isClosed_tsupport _)
    (closure_minimal (support_bumpR hR) isClosed_closedBall)

lemma hasTemperateGrowth_bumpR (hR : 0 < R) : HasTemperateGrowth (bumpR R (E := E)) :=
  (hasCompactSupport_bumpR hR).hasTemperateGrowth (contDiff_bumpR R)

/-- The derivatives of `bumpR R` vanish on the ball of radius `R` for `n ≥ 1` (where `bumpR R` is
locally constant equal to `1`). -/
lemma iteratedFDeriv_bumpR_eq_zero (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n) {x : E} (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ n (bumpR R) x = 0 := by
  have heq : (bumpR R : E → ℝ) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact bumpR_eq_one hR hy.le
  rw [(EventuallyEq.iteratedFDeriv ℝ heq n).eq_of_nhds, iteratedFDeriv_const_of_ne (by omega)]
  rfl

/-- Key scaling bound: differentiating `bumpR R = χ₀ (R⁻¹ • ·)` gains a factor `R⁻ⁿ`. -/
lemma norm_iteratedFDeriv_bumpR_le (hR : 0 < R) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (bumpR R) x‖ ≤ R⁻¹ ^ n * ‖iteratedFDeriv ℝ n (χ₀ : E → ℝ) (R⁻¹ • x)‖ := by
  grw [(by aesop : bumpR R = χ₀ ∘ (R⁻¹ • ContinuousLinearMap.id ℝ E)),
    iteratedFDeriv_comp_right _ (f := χ₀) bumpχ.contDiff x le_rfl,
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le, norm_smul, norm_id_le]
  simp [mul_comm, abs_of_pos hR]

end Bump

/-- The truncation of a Schwartz function `f` by the rescaled bump `bumpR R`; a compactly supported
Schwartz function that approximates `f` as `R → ∞`. -/
def truncate (R : ℝ) : 𝓢(E, F) := smulLeftCLM F (bumpR R) f

@[simp]
lemma truncate_apply (hR : 0 < R) (x : E) : truncate f R x = bumpR R x • f x :=
  smulLeftCLM_apply_apply (hasTemperateGrowth_bumpR hR) f x

lemma hasCompactSupport_truncate (hR : 0 < R) : HasCompactSupport (truncate f R : E → F) := by
  have hfun : (truncate f R : E → F) = (bumpR R : E → ℝ) • f := by
    funext x; exact truncate_apply f hR x
  simpa [hfun] using (hasCompactSupport_bumpR hR).smul_right

/-- **The heart of the argument.** For each seminorm index `(k, n)`, the seminorm of the truncation
error tends to `0` as `R → ∞`. -/
lemma tendsto_seminorm_truncate_sub (k n : ℕ) :
    Tendsto (fun R : ℝ => SchwartzMap.seminorm ℝ k n (truncate f R - f)) atTop (𝓝 0) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_iteratedFDeriv_χ₀ (E := E) n
  set A' : ℝ := max 1 A with hA'def
  have hA'1 : (1 : ℝ) ≤ A' := le_max_left _ _
  -- The constant controlling the truncation error.
  set C : ℝ := A' * ∑ i ∈ range (n + 1),
    (n.choose i : ℝ) * SchwartzMap.seminorm ℝ (k + 1) (n - i) f with hCdef
  have hbound : ∀ R : ℝ, 1 ≤ R →
      SchwartzMap.seminorm ℝ k n (truncate f R - f) ≤ C * R⁻¹ := by
    intro R hR1
    have hR : 0 < R := by linarith
    have hRinv0 : 0 ≤ R⁻¹ := by positivity
    have hRinv1 : R⁻¹ ≤ 1 := by simp [inv_le_one₀ hR, hR1]
    have hcoe : ⇑(truncate f R - f) = fun x => (bumpR R x - 1) • f x := by
      funext x; simp [truncate_apply f hR, sub_smul]
    refine seminorm_le_bound ℝ k n _ (by positivity) fun x => ?_
    rw [hcoe]
    -- Uniform bound on the derivatives of `bumpR R - 1`.
    have hbd : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i (bumpR R · - 1) x‖ ≤ A' := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_sub_comm,
          abs_of_nonneg (by linarith [bumpR_le_one R x])]
        linarith [bumpR_nonneg R x]
      · have hEq : iteratedFDeriv ℝ i (bumpR R · - 1) x = iteratedFDeriv ℝ i (bumpR R) x := by
          rw [show (bumpR R · - 1) = (bumpR R : E → ℝ) - fun _ => 1 from rfl,
            iteratedFDeriv_sub_apply
              ((contDiff_bumpR R).contDiffAt.of_le (mod_cast le_top)) contDiffAt_const,
            iteratedFDeriv_const_of_ne (by omega)]
          simp
        grw [hEq, norm_iteratedFDeriv_bumpR_le hR i x, pow_le_one₀ hRinv0 hRinv1, hA i hi _]
        grind
    rcases lt_or_ge ‖x‖ R with hxR | hxR
    · have hzero : iteratedFDeriv ℝ n (fun y ↦ (bumpR R y - 1) • f y) x = 0 := by
        have heq0 : (fun y ↦ (bumpR R y - 1) • f y) =ᶠ[𝓝 x] 0 := by
          filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hxR] with y hy
          simp [bumpR_eq_one hR hy.le]
        simp [(EventuallyEq.iteratedFDeriv ℝ heq0 n).eq_of_nhds]
      rw [hzero, norm_zero, mul_zero]; positivity
    · have : (0 : ℝ) < ‖x‖ := by linarith
      calc
        _ ≤ ‖x‖ ^ k * ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (bumpR R · - 1) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
            gcongr
            exact norm_iteratedFDeriv_smul_le ((contDiff_bumpR R).sub contDiff_const)
              (f.smooth ⊤) x (mod_cast le_top)
        _ = ∑ i ∈ range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (bumpR R · - 1) x‖ *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
            rw [mul_sum]; exact sum_congr rfl fun _ _ ↦ by ring
        _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * A' *
              (SchwartzMap.seminorm ℝ (k + 1) (n - i) f * R⁻¹) := by
            refine sum_le_sum fun _ _ ↦ ?_
            grw [hbd _ (by grind), ← le_seminorm ℝ _ _ f x, pow_succ, hxR]
            field_simp; rfl
        _ = _ := by simpa [hCdef, mul_sum, sum_mul] using sum_congr rfl fun _ _ ↦ by ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (h := (C * ·⁻¹)) tendsto_const_nhds
  · simpa using tendsto_inv_atTop_zero.const_mul C
  · filter_upwards with R using apply_nonneg _ _
  · filter_upwards [eventually_ge_atTop 1] with R hR using hbound R hR

/-- The truncations converge to `f` in the Schwartz topology as `R → ∞`. -/
lemma tendsto_truncate : Tendsto (truncate f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds (truncate f) f]
  rintro ⟨k, n⟩ ε hε
  simpa using (tendsto_seminorm_truncate_sub f k n).eventually (isOpen_Iio.mem_nhds hε)

/-- **Target.** Compactly supported Schwartz functions are dense in `𝓢(E, F)`. -/
theorem dense_hasCompactSupport :
    Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := by
  intro f
  refine mem_closure_of_tendsto (tendsto_truncate f) ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact hasCompactSupport_truncate f hR

end SchwartzMap
