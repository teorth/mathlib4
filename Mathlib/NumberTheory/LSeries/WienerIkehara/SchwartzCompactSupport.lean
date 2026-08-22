/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

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

## TODO

All proofs are currently `sorry`; this file is a design scaffold.
-/

@[expose] public section

open scoped Topology ContDiff
open Filter Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

/-- A fixed reference bump on `E`: equal to `1` on the closed unit ball, supported in `ball 0 2`. -/
def bumpχ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The reference bump rescaled by `R`: equal to `1` on `ball 0 R`, supported in `ball 0 (2R)`. -/
def bumpR (R : ℝ) (x : E) : ℝ := (bumpχ : ContDiffBump (0 : E)) (R⁻¹ • x)

section Bump

variable {R : ℝ}

@[simp] lemma bumpR_eq_one (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : bumpR R x = 1 := sorry

lemma bumpR_nonneg (R : ℝ) (x : E) : 0 ≤ bumpR R x := sorry

lemma bumpR_le_one (R : ℝ) (x : E) : bumpR R x ≤ 1 := sorry

lemma contDiff_bumpR (R : ℝ) : ContDiff ℝ ∞ (bumpR R : E → ℝ) := sorry

lemma support_bumpR (hR : 0 < R) :
    Function.support (bumpR R : E → ℝ) ⊆ closedBall (0 : E) (2 * R) := sorry

lemma hasCompactSupport_bumpR (hR : 0 < R) : HasCompactSupport (bumpR R : E → ℝ) := sorry

lemma hasTemperateGrowth_bumpR (hR : 0 < R) :
    Function.HasTemperateGrowth (bumpR R : E → ℝ) :=
  (hasCompactSupport_bumpR hR).hasTemperateGrowth (contDiff_bumpR R)

/-- The derivatives of `bumpR R` vanish on the ball of radius `R` for `n ≥ 1` (where `bumpR R` is
locally constant equal to `1`). -/
lemma iteratedFDeriv_bumpR_eq_zero (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n) {x : E} (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ n (bumpR R) x = 0 := sorry

/-- Key scaling bound: differentiating `bumpR R = χ (R⁻¹ • ·)` gains a factor `R⁻ⁿ`. -/
lemma norm_iteratedFDeriv_bumpR_le (R : ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (bumpR R) x‖
      ≤ R⁻¹ ^ n * ‖iteratedFDeriv ℝ n (fun y : E ↦ (bumpχ : ContDiffBump (0 : E)) y) (R⁻¹ • x)‖ :=
  sorry

end Bump

/-- The truncation of a Schwartz function `f` by the rescaled bump `bumpR R`; a compactly supported
Schwartz function that approximates `f` as `R → ∞`. -/
def truncate (f : 𝓢(E, F)) (R : ℝ) : 𝓢(E, F) := smulLeftCLM F (bumpR R) f

@[simp] lemma truncate_apply {R : ℝ} (hR : 0 < R) (f : 𝓢(E, F)) (x : E) :
    truncate f R x = bumpR R x • f x :=
  smulLeftCLM_apply_apply (hasTemperateGrowth_bumpR hR) f x

lemma hasCompactSupport_truncate {R : ℝ} (hR : 0 < R) (f : 𝓢(E, F)) :
    HasCompactSupport (truncate f R : E → F) := sorry

/-- **The heart of the argument.** For each seminorm index `(k, n)`, the seminorm of the truncation
error tends to `0` as `R → ∞`. -/
lemma tendsto_seminorm_truncate_sub (f : 𝓢(E, F)) (k n : ℕ) :
    Tendsto (fun R : ℝ => SchwartzMap.seminorm ℝ k n (truncate f R - f)) atTop (𝓝 0) := sorry

/-- The truncations converge to `f` in the Schwartz topology as `R → ∞`. -/
lemma tendsto_truncate (f : 𝓢(E, F)) :
    Tendsto (fun R : ℝ => truncate f R) atTop (𝓝 f) := sorry

/-- **Target.** Compactly supported Schwartz functions are dense in `𝓢(E, F)`. -/
theorem dense_hasCompactSupport :
    Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := sorry

end SchwartzMap
