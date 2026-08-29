/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Francisco Antonio Balderas, Vincent Beffara, Alex Kontorovich, Terence Tao,
  Ruben Van de Velde, Arend Mellendijk, Alastair Irving
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Topology.EMetricSpace.BoundedVariation

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.GRewrite.Elab
/-!
# The Wiener-Ikehara Tauberian theorem

Let `f : ℕ → ℝ` be non-negative with `∑ n ≤ x, f n ≪ x`, whose `L`-series `F` extends
continuously to `Re s ≥ 1` after subtracting `A / (s - 1)`.  Then
`∑ n < N, f n = A * N + o(N)`.

## Main results

* `WienerIkehara.tendsto_sum_div`: the Wiener-Ikehara Tauberian theorem.

The weak prime number theorem (`WeakPNT`) and its version in arithmetic progressions
(`WeakPNT_AP`), which are consequences, are in `Mathlib.NumberTheory.LSeries.WeakPNT`.

## Proof outline

Writing `ψ̂` for the Fourier transform, the proof studies `S σ ψ̂ x`, the difference
between `∑' n, term f σ n * ψ̂ (log (n / x) / (2 * π))` and its polar counterpart.  Rewriting both
halves as Fourier integrals (`sum_term_mul_fourier_eq`, `integral_exp_mul_fourier_eq`) cancels the
pole and expresses the S through `G` (`sum_term_mul_sub_mul_integral_eq`); letting `σ → 1`
and applying the Riemann-Lebesgue lemma gives `S 1 ψ̂ x → 0`, first for compactly supported
test functions (`limiting_cor`) and then for all Schwartz functions (`limiting_cor_schwartz`).
Surjectivity of the Fourier transform on Schwartz space upgrades this to a smoothed form of the
theorem (`wiener_ikehara_smooth`), and non-negativity of `f` together with a smooth Urysohn lemma
(`exists_contDiff_one_on_Icc_support_eq_Ioo`) replaces the smooth cutoff by the indicator of an
interval, whence the theorem (`tendsto_sum_div`).

This file is a draft port from the `PrimeNumberTheoremAnd` project.
-/

@[expose] public section

noncomputable section

open ArithmeticFunction hiding log
open Complex hiding log
open Real BigOperators MeasureTheory Filter Set FourierTransform LSeries Asymptotics SchwartzMap
  Function
open scoped Topology ContDiff ComplexConjugate

namespace SchwartzMap

/-- In the arguments of this file, it is convenient to isolate a bespoke seminorm for
Schwartz functions that controls the decay of their Fourier transform. -/
private def Q (ψ : 𝓢(ℝ, ℂ)) : ℝ := (𝓕 ψ).seminorm ℝ 0 0 + (𝓕 ψ).seminorm ℝ 2 0

private lemma Q_nonneg (ψ : 𝓢(ℝ, ℂ)) : 0 ≤ ψ.Q :=
  add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)

private lemma Q_continuous : Continuous Q :=
  (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp (by fun_prop)).add
    (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2, 0)).comp (by fun_prop))

private lemma decay_bound (ψ : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 ψ u‖ ≤ ψ.Q * (1 + u ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2)]
  have : ‖𝓕 ψ u‖ ≤ (𝓕 ψ).seminorm ℝ 0 0 := by
    simpa using SchwartzMap.le_seminorm (𝕜 := ℝ) 0 0 (𝓕 ψ) u
  have : u ^ 2 * ‖𝓕 ψ u‖ ≤ (𝓕 ψ).seminorm ℝ 2 0 := by
    simpa [norm_eq_abs, sq_abs, norm_iteratedFDeriv_zero] using
      SchwartzMap.le_seminorm (𝕜 := ℝ) 2 0 (𝓕 ψ) u
  unfold Q
  nlinarith

end SchwartzMap

/-- It is convenient to automatically coerce real-valued functions to complex-valued functions. -/
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n ↦ f n⟩

/-- The data and hypotheses for the Wiener--Ikehara theorem.  Can be conveniently accessed inside
the `WienerIkehara` namespace by adding a `[WienerIkehara]` instance.

The `hf` hypothesis can be derived from `bound`, and `bound` and `hA` are in fact redundant; but
implementing these simplifications is non-trivial, and the hypotheses can usually be easily
verified from existing API in practice anyway. -/
class WienerIkehara where
  /-- The function being estimated. -/
  f : ℕ → ℝ
  /-- The constant in the Chebyshev-type bound. -/
  C : ℝ
  bound : ∀ n, ∑ i ∈ .range n, ‖f i‖ ≤ C * n
  /-- The asymptotic constant. -/
  A : ℝ
  hA : 0 ≤ A
  /-- The continuous extension of `s ↦ LSeries f s - A / (s - 1)` to `re s ≥ 1`. -/
  G : ℂ → ℂ
  hG : ContinuousOn G {s | 1 ≤ s.re}
  hG' : EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}
  hf : ∀ (σ : ℝ), 1 < σ → LSeriesSummable f σ
  hpos : 0 ≤ f

namespace WienerIkehara

private abbrev c₀ := π⁻¹ * 2⁻¹

private lemma C_nonneg [WienerIkehara] : 0 ≤ C := (norm_nonneg (f 0)).trans (by simpa using bound 1)
section FourierIdentities

variable [WienerIkehara]

private def S₁ (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ := ∑' n, term f σ n * φ (c₀ * log (n / x))

private def S₂ (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  A * ↑(x ^ (1 - σ)) * ∫ u in Ici (- log x), rexp (-u * (σ - 1)) * φ (c₀ * u)

/-- A key S in the Wiener--Ikehara analysis involving an exponent `σ`, a test
function `φ`, and a scale parameter `x`. -/
private def S (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ := S₁ σ φ x - S₂ σ φ x

variable {x σ : ℝ} (ψ : 𝓢(ℝ, ℂ))

private lemma sum_term_mul_fourier_eq (hx : 0 < x) (hσ : 1 < σ) :
    S₁ σ (𝓕 ψ) x = ∫ t : ℝ, LSeries f (σ + t * I) * ψ t * x ^ (t * I) :=
  calc
    _ = ∑' n, ∫ t, term f σ n * 𝐞 (-(c₀ * log (n / x) * t)) • ψ t := by
      simp [S₁, ψ.fourier_coe, fourier_eq, integral_const_mul]
    _ = ∫ t, ∑' n, _ := by
      refine (integral_tsum (by fun_prop) ?_).symm
      have (n : ℕ) : AEMeasurable fun t ↦
        (‖fourierChar (-(c₀ * log (n / x) * t)) • ψ t‖ₑ : ENNReal) := by fun_prop
      simp_rw [enorm_mul, lintegral_const_mul'' _ (this _), Circle.enorm_smul,
        ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ (ne_top_of_lt ψ.integrable.2)
      simp_rw [enorm_eq_nnnorm, ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal,
          NNReal.summable_coe, (hf σ hσ).norm.toNNReal]
    _ = _ := by
      congr with y
      rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries,
        ← Summable.tsum_smul_const]
      · congr with n
        by_cases hn : n = 0
        · simp [*]
        suffices cexp (-(2 * π * ((↑π)⁻¹ * 2⁻¹ * log (n / x) * y) * I))
            = x ^ (y * I) / n ^ (y * I) by
          simp [Circle.smul_def, fourierChar_apply, hn, cpow_add, field, this]
        simp [cpow_def_of_ne_zero, hx.ne.symm, hn, ← Complex.exp_sub, log_div, ofReal_log, hx.le]
        congr
        field_simp
        grind
      · exact (hf σ hσ).of_re_le_re (by simp)

private lemma integral_exp_mul_fourier_eq (hx : 0 < x) (hσ : 1 < σ) :
    S₂ σ (𝓕 ψ) x = A * ∫ t, (1 / (σ + t * I - 1)) * ψ t * x^(t * I) ∂volume := by
  unfold S₂; rw [mul_assoc]; congr 1
  calc
  _ = ↑(x ^ (1 - σ)) * ∫ u in Ici (-log x),
      ∫ a, (rexp (-u * (σ - 1)) : ℂ) • 𝐞 (-(a * (c₀ * u))) • ψ a := by
    simp_rw [ψ.fourier_coe, fourier_real_eq, ← smul_eq_mul, ← integral_smul]
  _ = ↑(x ^ (1 - σ)) * ∫ a, ∫ u in _, _ := by
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-log x))).prod volume
    congr 1
    suffices Integrable (uncurry fun u a ↦ ((rexp (-u * (σ - 1))) : ℂ) •
      (𝐞 (-(a * (c₀ * u))) : ℂ) • ψ a) ν from integral_integral_swap this
    refine ⟨ by fun_prop, ?_ ⟩
    let f1 := fun (a1 : ℝ) ↦ ‖cexp (-(a1 * (σ - 1)))‖ₑ
    let f2 := (‖ψ ·‖ₑ)
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, uncurry]
    grw [lintegral_prod_mul (by fun_prop) (by fun_prop)]
    suffices IntegrableOn _ (Ici (-log x)) from ENNReal.mul_lt_top this.2 ψ.integrable.2
    norm_cast
    refine .ofReal ?_
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
    exact exp_neg_integrableOn_Ioi _ (by linarith)
  _ = _ := by
    rw [← integral_const_mul]
    congr; ext t
    have : (x : ℂ) ≠ 0 := mod_cast hx.ne.symm
    calc
      _ = ↑(x ^ (1 - σ)) * ((∫ u in Ici (-log x), cexp ((1 - σ - t * I) * u)) * ψ t) := by
        rw [← integral_mul_const]
        congr
        push_cast
        simp only [ofReal_neg, ofReal_mul, Circle.smul_def, fourierChar_apply, ← mul_assoc,
          ofReal_ofNat, smul_eq_mul, ← Complex.exp_add, ofReal_inv]
        field_simp
        grind
      _ = ↑(x ^ (1 - σ)) * (((x:ℂ) ^ (σ - 1 : ℂ) * x ^ (t * I)) * (1 / (σ + t * I - 1)) * ψ t) := by
        rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi (by simp [hσ]), ofReal_neg,
          division_def, neg_mul_comm, ofReal_log hx.le]
        congr 3
        · rw [← cpow_add _ _ this, cpow_def_of_ne_zero this]
          ring_nf
        · grind
      _ = _ := by
        field_simp
        rw [ofReal_cpow hx.le, ofReal_sub, ← cpow_add _ _ this]
        ring_nf
        simp

/-- The main result of this section: an initial Fourier identity expressing a S of
`f` as an error term of Fourier integral type. -/
private lemma sum_term_mul_sub_mul_integral_eq {ψ : 𝓢(ℝ, ℂ)}
    (hψ : HasCompactSupport ψ) (hx : 1 ≤ x) (σ : ℝ) (hσ : 1 < σ) :
    S σ (𝓕 ψ) x = ∫ t : ℝ, G (σ + t * I) * ψ t * x ^ (t * I) := by
  have hx' : 0 < x := by linarith
  simp_rw [S, sum_term_mul_fourier_eq ψ hx' hσ, integral_exp_mul_fourier_eq ψ hx' hσ]
  have (u : ℝ) : σ + u * I - 1 ≠ 0 := by
    intro h; have := congr(re $h); simp at this; linarith
  have : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (by fun_prop) (by simp [hx'])
  rw [← integral_const_mul, ← integral_sub]
  · refine integral_congr_ae (.of_forall fun u ↦ ?_)
    simp_rw [hG' (by simp [hσ] : 1 < (σ + u * I).re)]
    field_simp
  · have : Continuous fun x : ℝ ↦ LSeries f (σ + x * I) := by
      refine continuous_tsum (fun i ↦ ?_) (hf _ hσ).norm (by simp [norm_term_eq])
      by_cases h : i = 0
      · simpa [h] using continuous_const
      · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
          (by simp [h])
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hψ.mul_left.mul_right
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hψ.mul_left.mul_right.mul_left

end FourierIdentities

section HelperFunctions

variable {a c t x : ℝ}

private def F₂ (t : ℝ) : ℝ := (t * (1 + (c₀ * log t) ^ 2))⁻¹

private lemma F₂_nonneg (ht : 0 ≤ t) : 0 ≤ F₂ t := by unfold F₂; positivity

private lemma F₂_deriv (ht : t ≠ 0) : HasDerivAt F₂
    (- (c₀ ^ 2 * (log t + 1) ^ 2 + (1 - c₀) * (1 + c₀)) * F₂ t ^ 2) t := by
  have : HasDerivAt (fun t ↦ t * (1 + (c₀ * log t) ^ 2))
      (1 + 2 * c₀ ^ 2 * log t + (c₀ * log t) ^ 2) t := by
    convert! (hasDerivAt_id' t).mul ?_ (d' := 2 * c₀ ^ 2 * t⁻¹ * log t) using 1
    · grind
    convert! (((hasDerivAt_log ht).const_mul _).pow (f' := c₀ * t⁻¹) 2).const_add _ using 1
    ring
  convert! this.inv (mul_ne_zero ht (ne_of_lt (by positivity)).symm) using 1
  simp only [F₂]; grind

private lemma F₂_antitone : AntitoneOn F₂ (Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _)
    (fun _ _ ↦ (F₂_deriv (by grind)).continuousAt.continuousWithinAt)
    (fun _ _ ↦ (F₂_deriv (fun _ ↦ by simp_all)).hasDerivWithinAt)
    (fun x _ ↦ ?_)
  have : 0 < c₀ ^ 2 * (log x + 1) ^ 2 + (1 - c₀) * (1 + c₀) := by
    have : π⁻¹ ≤ 2⁻¹ := by field_simp; exact two_le_pi
    have : 0 < 1 - π⁻¹ * 2⁻¹ := by nlinarith
    positivity
  simp only [neg_mul, Left.neg_nonpos_iff]
  positivity

private lemma F₄_le_one (hx : 0 < x) (i : ℕ) : x⁻¹ * F₂ (i / x) ≤ 1 := by
  unfold F₂
  by_cases hi : i = 0
  · simp [hi]
  grw [← sq_nonneg, ← (mod_cast by omega : 1 ≤ (i : ℝ))]
  simp [field]

private lemma F₂_div_eq (hc : 0 < c) (ht : 0 < t) :
    a * F₂ (t / c) = t⁻¹ • (a * c * (1 + (c₀ * (log t - log c)) ^ 2)⁻¹) := by
  have : (0:ℝ) < 1 + (c₀ * (log t - log c)) ^ 2 := by positivity
  simp [F₂, log_div ht.ne' hc.ne', field]

private lemma F₂_integrable (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * F₂ (t / c)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact ((integrableOn_comp_log_Ioi_zero _).2
    (((integrable_inv_one_add_mul_sq (by positivity)).comp_sub_right _).const_mul _)).congr_fun
    (fun t ht ↦ (F₂_div_eq hc ht).symm) measurableSet_Ioi

private lemma l5 {n : ℕ} (hx : 0 < x) : AntitoneOn (fun t ↦ x⁻¹ * F₂ (t / x))
    (Ioc 0 n) := by
  intro u ⟨_, _⟩ v ⟨_, _⟩ huv
  apply mul_le_mul le_rfl ?_ (F₂_nonneg (by positivity)) (by positivity)
  exact F₂_antitone (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity) (by grw [huv])

private lemma l6 {n : ℕ} (hx : 0 < x) : IntegrableOn (fun t ↦ x⁻¹ * F₂ (t / x))
    (Icc 0 n) volume := .mono_set (F₂_integrable (by positivity)) Icc_subset_Ici_self

end HelperFunctions

section LimitingFourierIdentity

set_option backward.isDefEq.respectTransparency false in
private lemma limiting_cor_aux {ψ : ℝ → ℂ} :
    Tendsto (fun x : ℝ ↦ ∫ t, ψ t * x ^ (t * I)) atTop (𝓝 0) := by
  have : ∀ᶠ x : ℝ in atTop, ∫ t, ψ t * x ^ (t * I) = ∫ t, ψ t * exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx'
    refine integral_congr_ae (Eventually.of_forall (fun _ ↦ ?_))
    simp [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx']
    ring_nf; simp
  simp_rw [tendsto_congr' this]
  convert_to Tendsto (fun x ↦ 𝓕 ψ (-c₀ * log x)) atTop (𝓝 0)
  · ext; congr; ext
    simp only [← ofReal_mul, mul_comm (ψ _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg]
    congr; norm_cast; field_simp
  refine (zero_at_infty_fourier ψ).comp <| Tendsto.mono_right ?_ atBot_le_cocompact
  exact tendsto_log_atTop.const_mul_atTop_of_neg (by simp [pi_pos])

private abbrev C₀ := 1 + ∫ t in Ioi 0, F₂ t

private lemma C₀_nonneg : 0 ≤ C₀ :=
  add_nonneg zero_le_one (setIntegral_nonneg measurableSet_Ioi (fun _ hx ↦ F₂_nonneg hx.le))

variable {x : ℝ} (Ψ : 𝓢(ℝ, ℂ)) [WienerIkehara]

private lemma bound_sum_log_range (hx : 1 ≤ x) (n) :
    ∑ i ∈ .range n, ‖f i‖ / i * (1 + (c₀ * log (i / x)) ^ 2)⁻¹ ≤ C * C₀ := by
  let F₅ (i : ℕ) := if i = 0 then 1 else x⁻¹ * F₂ (i / x)
  have l0 : 0 < x := by linarith
  have := C_nonneg
  calc
    _ ≤ ∑ i ∈ .range n, ‖f i‖ * F₅ i := by
      gcongr 1 with i
      by_cases hi : i = 0 <;> simp [hi, F₅, F₂, field]
    _ ≤ C * ∑ i ∈ .range n, F₅ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_mul_le_sum_mul_of_sum_range_le (fun k _ ↦ by simpa [mul_comm] using bound k)
      · intro i
        by_cases hi : i = 0 <;> simp only [F₂, hi, ↓reduceIte, F₅, Pi.zero_apply] <;> positivity
      · intro i j _; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
          simp only [hj, ↓reduceIte, hi, le_refl, F₅, F₄_le_one l0]
        · omega
        · gcongr
          apply F₂_antitone _ _ (by gcongr) <;> simp only [mem_Ioi] <;> positivity
    _ ≤ _ := by
      gcongr; simp only [F₅]
      by_cases h : n = 0
      · simp [h, C₀_nonneg]
      have : Finset.range n = {0} ∪ .Ico 1 n := by grind
      simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
        false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
      convert_to! ∑ i ∈ .Ico 1 n, x⁻¹ * F₂ (i / x) ≤ _
      · exact Finset.sum_congr rfl (by grind)
      simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
      trans ∫ t in 0..↑(n - 1), x⁻¹ * F₂ (t / x)
      · simpa using @AntitoneOn.sum_le_integral_of_integrableOn 0 (n - 1)
          (fun t ↦ x⁻¹ * F₂ (t / x)) (by simpa using l5 (by positivity))
          (by simpa using l6 (by positivity))
      rw [intervalIntegral.integral_comp_div (x⁻¹ * F₂ ·) l0.ne.symm]
      simp only [intervalIntegral.integral_const_mul]
      have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
      simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, this, ↓reduceIte, uIoc_of_le,
        smul_eq_mul, one_mul, zero_div, mul_inv_cancel₀ l0.ne.symm, ← mul_assoc]
      apply integral_mono_measure
      · exact Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
      · exact eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) fun x hx ↦ F₂_nonneg hx.le
      · simpa using! (F₂_integrable (a := 1) zero_lt_one).mono_set Ioi_subset_Ici_self

private lemma summable_sum_log_range (hx : 1 ≤ x) :
  Summable fun n ↦ ‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹ :=
    summable_of_sum_range_le (fun _ ↦ by positivity)
    (fun n ↦ by simpa using bound_sum_log_range hx n)

private theorem limiting_fourier_lim1 (hx : 1 ≤ x) : Tendsto (fun σ : ℝ ↦ S σ (𝓕 Ψ) x) (𝓝[>] 1)
      (𝓝 (S 1 (𝓕 Ψ) x)) := by
  unfold S S₁
  apply Tendsto.sub
  · refine tendsto_tsum_of_dominated_convergence ((summable_sum_log_range hx).mul_left Ψ.Q)
      (fun n ↦ ?_) ?_
    · apply Tendsto.mul_const
      by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, tendsto_const_nhds_iff]
      refine tendsto_const_nhds.div ?_ (by simp [h])
      simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
    · rw [eventually_nhdsWithin_iff]
      apply Eventually.of_forall
      intro σ (hσ : 1 < σ) n
      by_cases h : n = 0
      · simp [h]
      simp only [norm_mul, ofReal_re, h, ↓reduceIte, norm_term_eq]
      grw [Ψ.decay_bound, ← hσ]
      · simp; grind
      · exact_mod_cast (by omega)
      · positivity [Ψ.Q_nonneg]
  · apply Tendsto.mul
    · suffices Tendsto (fun σ : ℝ ↦ x ^ (1 - σ)) (𝓝[>] 1) (𝓝 1) by
        simpa using ((continuous_ofReal.tendsto 1).comp this).const_mul ↑A
      have : Tendsto (fun σ : ℝ ↦ σ) (𝓝 1) (𝓝 1) := fun _ a ↦ a
      have : Tendsto (fun σ : ℝ ↦ 1 - σ) (𝓝[>] 1) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
      simpa using tendsto_const_nhds.rpow this (by grind)
    have : Integrable (fun t ↦ max |x| 1 * (Ψ.Q / (1 + (c₀ * t) ^ 2)))
        (volume.restrict (Ici (-log x))) := by
      simp_rw [div_eq_mul_inv]
      exact (((integrable_inv_one_add_sq.comp_mul_left'
        (by positivity)).const_mul _).const_mul _).restrict
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ this ?_
    · have := (𝓕 Ψ).continuous
      exact Eventually.of_forall (fun _ ↦ Continuous.aestronglyMeasurable (by continuity))
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem; simp
      · intro σ ⟨_, _⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - log x ≤ t)
        rw [norm_mul]
        refine mul_le_mul ?_ (Ψ.decay_bound _) (norm_nonneg _) (by grind [abs_nonneg])
        norm_cast
        have := log_nonneg hx
        grw [norm_eq_abs, abs_exp, ← ht, neg_neg, (by linarith : σ - 1 ≤ 1)]
        grind [Real.exp_log, abs_of_nonneg]
    · refine Eventually.of_forall fun x ↦ ?_
      suffices Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝 1) (𝓝 1) by
        simpa using Tendsto.mono_left (this.mul_const _) nhdsWithin_le_nhds
      suffices Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using this.tendsto 1
      continuity

private theorem limiting_fourier_lim3 {Ψ : 𝓢(ℝ, ℂ)} (hΨ : HasCompactSupport Ψ) (hx : 1 ≤ x) :
    Tendsto (fun σ : ℝ ↦ ∫ t : ℝ, G (σ + t * I) * Ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * Ψ t * x ^ (t * I))) := by
  by_cases h : tsupport Ψ = ∅
  · simp [tsupport_eq_empty_iff.mp h]
  obtain ⟨a₀, ha₀⟩ := nonempty_iff_ne_empty.mpr h
  have l1 : IsCompact (reProdIm (Icc 1 2) (tsupport Ψ)) := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport Ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm hΨ.isBounded
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn ⟨1 + a₀ * I, by simp [mem_reProdIm, ha₀]⟩
    (hG.mono (fun z hz ↦ (mem_reProdIm.mp hz).1.1)).norm
  apply tendsto_integral_filter_of_dominated_convergence (bound := (‖G z‖ * ‖Ψ ·‖))
  · refine eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
      fun u hu ↦ (Continuous.mul ?_ ?_).aestronglyMeasurable
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul Ψ.continuous
    · apply Continuous.const_cpow (by fun_prop); simp; linarith
  · refine eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
      fun u hu ↦ Eventually.of_forall fun v ↦ ?_
    by_cases h : v ∈ tsupport Ψ
    · grw [norm_mul, norm_mul, isMaxOn_iff.mp hmax _ (by simp [mem_reProdIm, hu.1, hu.2, h])]
      have : (x : ℂ) ≠ 0 := mod_cast by linarith
      have : arg x = 0 := by simp [arg_eq_zero_iff]; linarith
      simp [norm_cpow_of_ne_zero, *]
    · have : v ∉ support Ψ := by grind [subset_tsupport]
      simp_all
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hΨ.norm.mul_left
  · apply Eventually.of_forall; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG _ (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

private lemma limiting_cor {Ψ : 𝓢(ℝ, ℂ)} (hΨ : HasCompactSupport Ψ) :
    Tendsto (S 1 (𝓕 Ψ)) atTop (𝓝 0) := by
  apply (limiting_cor_aux (ψ := fun t ↦ G (1 + t * I) * (Ψ t))).congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  unfold S
  apply (tendsto_nhds_unique_of_eventuallyEq (limiting_fourier_lim1 Ψ hx)
    (limiting_fourier_lim3 hΨ hx) _).symm
  simpa [eventuallyEq_nhdsWithin_iff] using!
    Eventually.of_forall (sum_term_mul_sub_mul_integral_eq hΨ hx)

end LimitingFourierIdentity

section LimitingFourierIdentitySchwartz

variable (Ψ : 𝓢(ℝ, ℂ))

private lemma summable_fourier_aux (x) (f : ℕ → ℂ) (n) : ‖(term f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ ≤
      Ψ.Q * (‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (Ψ.decay_bound (1 / (2 * π) * log (n / x)))
    (norm_nonneg (f n / n)) using 1
  · simp [term_of_ne_zero']
  · simp; grind

private lemma bound_I2 (x : ℝ) : ‖∫ u in Ici (-log x), 𝓕 Ψ (c₀ * u)‖ ≤ Ψ.Q * (2 * π ^ 2) := by
  have key a : ‖𝓕 Ψ (c₀ * a)‖ ≤ Ψ.Q * (1 + (c₀ * a) ^ 2)⁻¹ := Ψ.decay_bound _
  have := Ψ.Q_nonneg
  have : Integrable fun a ↦ (1 + (c₀ * a) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' (by positivity)
  grw [norm_integral_le_integral_norm, setIntegral_mono ((this.const_mul Ψ.Q).mono' (by fun_prop)
    (by simp [key])).integrableOn (this.const_mul _).integrableOn key, integral_const_mul,
    setIntegral_le_integral this, Measure.integral_comp_mul_left fun x ↦ (1 + x ^ 2)⁻¹]
  · have : 0 ≤ 2 * π := by simp [pi_nonneg]
    simp [abs_eq_self.mpr this]; grind
  · exact Eventually.of_forall fun _ ↦ by positivity

variable {x : ℝ} [WienerIkehara]

private lemma summable_fourier (hx : 1 ≤ x) :
    Summable fun n ↦ ‖(term f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (summable_fourier_aux Ψ x f)
    (by simpa using (summable_sum_log_range hx).const_smul Ψ.Q)

private lemma bound_I1 (hx : 1 ≤ x) : ‖S₁ 1 (𝓕 Ψ) x‖ ≤
    Ψ.Q • ∑' n, ‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹ := by
  have l5 : Summable fun n ↦ ‖f n‖ / n * ((1 + (c₀ * (log (n / x))) ^ 2)⁻¹) := by
    simpa using summable_sum_log_range hx
  have l1 : Summable fun n ↦ ‖(term f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ :=
    summable_fourier Ψ hx
  unfold S₁
  apply (norm_tsum_le_tsum_norm l1).trans
  grw [Summable.tsum_mono l1 (by simpa using l5.const_smul Ψ.Q) (summable_fourier_aux Ψ x f)
    , ← Summable.tsum_const_smul _ l5]
  simp

private lemma bound_I1' (hx : 1 ≤ x) : ‖S₁ 1 (𝓕 Ψ) x‖ ≤ Ψ.Q * C * C₀ := by
  grw [bound_I1 Ψ hx, smul_eq_mul, mul_assoc]
  refine mul_le_mul le_rfl ?_ (tsum_nonneg (fun _ ↦ by positivity)) Ψ.Q_nonneg
  calc
    _ ≤ _ := tsum_le_of_sum_range_le (fun _ ↦ by positivity) (bound_sum_log_range hx)
    _ = _ := by congr

private lemma limiting_cor_schwartz : Tendsto (S 1 (𝓕 Ψ)) atTop (𝓝 0) := by
  simp_rw [Metric.tendsto_nhds]; intro ε hε
  have hψmem : (Ψ - Ψ).Q < (ε / 2) / (max 1 (C * C₀ + |A| * (2 * π ^ 2))) := by
    simp only [Q, sub_self, FourierTransform.fourier_zero, _root_.map_zero, add_zero]; positivity
  obtain ⟨φ, hφQ : (Ψ - φ).Q < _, hφcs⟩ :=
    SchwartzMap.dense_hasCompactSupport.inter_open_nonempty _
    (isOpen_lt (SchwartzMap.Q_continuous.comp (by fun_prop)) continuous_const) ⟨Ψ, hψmem⟩
  have := limiting_cor hφcs
  simp_rw [Metric.tendsto_nhds, dist_zero_right] at this
  filter_upwards [eventually_ge_atTop 1, this (ε / 2) (by positivity)] with x hx _
  have hFsub (t : ℝ) : 𝓕 (Ψ - φ) t = 𝓕 Ψ t - 𝓕 φ t := by
    simp_rw [← fourierTransformCLM_apply ℂ, map_sub, sub_apply]
  have : S₁ 1 (𝓕 (Ψ - φ)) x = S₁ 1 (𝓕 Ψ) x - S₁ 1 (𝓕 φ) x := by
    unfold S₁; rw [ofReal_one, ← Summable.tsum_sub]
    · exact tsum_congr fun _ ↦ by rw [hFsub]; ring
    · simpa [← summable_norm_iff] using summable_fourier Ψ hx
    · simpa [← summable_norm_iff] using summable_fourier φ hx
  have : S₂ 1 (𝓕 (Ψ - φ)) x = S₂ 1 (𝓕 Ψ) x - S₂ 1 (𝓕 φ) x := by
    simp only [S₂, sub_self, rpow_zero, ofReal_one, mul_one, mul_zero, Real.exp_zero,
      one_mul]
    rw [← mul_sub, ← integral_sub]
    · congr 1
      exact setIntegral_congr_fun measurableSet_Ici fun _ _ ↦ hFsub _
    · exact ((𝓕 Ψ).integrable.comp_mul_left' (by positivity)).restrict
    · exact ((𝓕 φ).integrable.comp_mul_left' (by positivity)).restrict
  have : S 1 (𝓕 Ψ) x = S 1 (𝓕 (Ψ - φ)) x + S 1 (𝓕 φ) x := by
    unfold S; grind
  have : ‖S 1 (𝓕 (Ψ - φ)) x‖ ≤ ε / 2 := by
    unfold S S₂
    grw [norm_sub_le, bound_I1' _ hx, norm_mul]
    simp only [sub_self, rpow_zero, ofReal_one, mul_one, norm_real, norm_eq_abs, mul_zero,
      Real.exp_zero, one_mul]
    have := C_nonneg
    have := C₀_nonneg
    grw [bound_I2 (Ψ - φ) x, hφQ]
    field_simp; grind
  grind [dist_zero_right, norm_add_le]

end LimitingFourierIdentitySchwartz

section Smooth

variable {ψ : ℝ → ℂ}

private lemma comp_exp_support0 (hplus : closure (support ψ) ⊆ Ioi 0) : ∀ᶠ x in 𝓝 0, ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ lt_irrefl 0 <| mem_Ioi.mp (hplus h))

private theorem comp_exp_support (hsupp : HasCompactSupport ψ)
    (hplus : closure (support ψ) ⊆ Ioi 0) : HasCompactSupport (ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp ⊢
  exact ⟨tendsto_exp_atBot <| comp_exp_support0 hplus, tendsto_exp_atTop hsupp.2⟩

variable [WienerIkehara]

/-- A smoothed *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `f` behaves like `A` asymptotically
with respect to smooth weights. -/
lemma tendsto_sum_div_smooth (hsmooth : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    (hplus : closure (support ψ) ⊆ Ioi 0) : Tendsto (fun x ↦ (∑' n, f n * ψ (n / x)) / x)
    atTop (𝓝 (A * ∫ y in Ioi 0, ψ y)) := by
  let h (x) := rexp (2 * π * x) * ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ fun x ↦ rexp (2 * π * x) := (contDiff_const.mul contDiff_id).exp
    exact (ofRealCLM.contDiff.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ : ∃ g, 𝓕 g = h2.toSchwartzMap h1 := ⟨𝓕⁻ _, fourier_fourierInv_eq _⟩
  have {y} (hy : 0 < y) : y * ψ y = 𝓕 g (c₀ * log y) := by
    simp only [hg, HasCompactSupport.toSchwartzMap_toFun, h]
    field_simp
    rw [Real.exp_log hy]
  have l2 : ∀ᶠ x in atTop, S 1 (𝓕 g) x =
      ∑' n, f n * ψ (n / x) / x - A * ∫ y in Ioi x⁻¹, ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    unfold S S₁
    congr
    · ext n
      by_cases hn : n = 0
      · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
      rw [← this (by positivity)]
      have : (n : ℂ) ≠ 0 := by simpa using hn
      have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
      simp [ofReal_div, ofReal_natCast, term, hn]
      field_simp
    · simp [S₂, hg, HasCompactSupport.toSchwartzMap_toFun, h]
      field_simp; norm_cast
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
      left
      have hcont := hsmooth.continuous
      have : HasCompactSupport (rexp • (ψ ∘ rexp)) := (comp_exp_support hsupp hplus).smul_left
      simpa [Real.exp_neg, exp_log hx] using integral_deriv_smul_comp_Ioi (by fun_prop)
        tendsto_exp_atTop (fun t _ ↦ (Real.hasDerivAt_exp t).hasDerivWithinAt)
        (by fun_prop) (hcont.integrable_of_hasCompactSupport hsupp).integrableOn
        ((Continuous.integrable_of_hasCompactSupport (by fun_prop) this).integrableOn :
        IntegrableOn _ (Ici (-log x)) _)
  have : Tendsto (fun x ↦ (A * ∫ y in Ioi x⁻¹, ψ y) - A * ∫ y in Ioi 0, ψ y) atTop (𝓝 0) := by
    obtain ⟨ε, _, _⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
    have h1 : Integrable ψ := hsmooth.continuous.integrable_of_hasCompactSupport hsupp
    apply tendsto_nhds_of_eventually_eq; filter_upwards [eventually_gt_atTop ε⁻¹] with x _
    simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub,
      ← integral_sub (h1.indicator measurableSet_Ioi) (h1.indicator measurableSet_Ioi)]
    simp only [mul_eq_zero, ofReal_eq_zero]
    refine Or.inr (integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_))
    have : 0 < ε⁻¹ := by positivity
    have : 0 < x := by linarith
    have : 0 < x⁻¹ := by positivity
    rw [(by grind : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹), indicator_union_of_disjoint (by simp) ψ,
      Pi.zero_apply]
    by_cases ht : t ∈ Ioc 0 x⁻¹
    · simp_all; grind [inv_lt_comm₀]
    simp [ht]
  simpa [tendsto_sub_nhds_zero_iff, tsum_div_const] using ((limiting_cor_schwartz g).congr' l2).add
    this

/-- A version of smoothed Wiener--Ikehara for real-valued cutoffs. -/
lemma tendsto_sum_div_smooth_real {Ψ : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : closure (support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Ioi 0, Ψ y)) := by
  have : Tendsto (fun x ↦ (∑' n, f n * (ofReal ∘ Ψ) (n / x)) / x) atTop
      (nhds (A * ∫ y in Ioi 0, (ofReal ∘ Ψ) y)) := tendsto_sum_div_smooth
      (ofRealCLM.contDiff.comp hsmooth) (hsupp.comp_left rfl) (by rwa [support_comp_eq]; simp)
  have := (continuous_re.tendsto _).comp this
  simp at this; norm_cast at this

end Smooth

variable {a b c d : ℝ}

/-- A smooth Urysohn lemma on the real line: for `a < b` and `c < d` there is a smooth compactly
supported function squeezed between the indicators of `Icc b c` and `Ioo a d`, whose support is
exactly `Ioo a d`.  This specializes `exists_contMDiff_support_eq_eq_one_iff`. -/
lemma exists_contDiff_one_on_Icc_support_eq_Ioo (hab : a < b) (hcd : c < d) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧
      indicator (Icc b c) 1 ≤ Ψ ∧ Ψ ≤ indicator (Ioo a d) 1 ∧ support Ψ = Ioo a d := by
  obtain ⟨Ψ, hsmooth, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := modelWithCornersSelf ℝ ℝ)
      isOpen_Ioo isClosed_Icc (Icc_subset_Ioo hab hcd)
  exact ⟨Ψ, hsmooth.contDiff, .of_support_subset_isCompact isCompact_Icc
    (hsupp ▸ Ioo_subset_Icc_self), indicator_le' (fun x hx ↦ ((hone x).mp hx).ge)
    fun x _ ↦ (hrange (mem_range_self x)).1, fun x ↦ le_indicator_apply
    (fun _ ↦ (hrange (mem_range_self x)).2) (by grind [mem_support]), hsupp⟩

/-- A version of `exists_contDiff_one_on_Icc_support_eq_Ioo` for cutoffs supported away from the
origin, additionally controlling the integral of the cutoff from above and below by the lengths of
`Ioo a d` and `Icc b c` respectively. -/
private lemma exists_cutoff (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    ∃ ψ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ closure (support ψ) ⊆ Ioi 0 ∧
      indicator (Icc b c) 1 ≤ ψ ∧ ψ ≤ indicator (Ioo a d) 1 ∧
      c - b ≤ ∫ y in Ioi 0, ψ y ∧ ∫ y in Ioi 0, ψ y ≤ d - a := by
  have had : a < d := hab.trans_le (hbc.trans hcd.le)
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := exists_contDiff_one_on_Icc_support_eq_Ioo hab hcd
  have hsupp : closure (support ψ) ⊆ Ioi 0 := by simp [h5, had.ne, Icc_subset_Ioi_iff had.le, ha]
  have hψ : Integrable ψ := h1.continuous.integrable_of_hasCompactSupport h2
  have hfull : ∫ y in Ioi 0, ψ y = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      notMem_support.1 fun h ↦ hx (hsupp (subset_closure h))
  have hind {s} (hs : MeasurableSet s) (hs' : volume s ≠ ⊤) :
      Integrable (indicator s (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff hs).2 (integrableOn_const hs')
  refine ⟨ψ, h1, h2, hsupp, h3, h4, ?_, ?_⟩
  · rw [hfull, ← volume_real_Icc_of_le hbc, ← integral_indicator_one measurableSet_Icc]
    exact integral_mono (hind measurableSet_Icc (by simp)) hψ h3
  · rw [hfull, ← volume_real_Ioo_of_le had.le, ← integral_indicator_one measurableSet_Ioo]
    exact integral_mono hψ (hind measurableSet_Ioo (by simp)) h4

variable {x : ℝ} {g : ℝ → ℝ} [WienerIkehara]

private lemma WI_summable (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable fun n ↦ f n * g (n / x) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold HasFiniteSupport
  simp only [support_mul]; apply Finite.inter_of_right; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi ↦ by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

/-- The *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/
theorem tendsto_sum_div : Tendsto (fun N ↦ (∑ i ∈ .range N, f i) / N) atTop (𝓝 A) := by
  have hI {u v} (huv : u < v) : HasCompactSupport (indicator (Ico u v) (1 : ℝ → ℝ)) := by
    simpa [HasCompactSupport, tsupport, huv.ne] using isCompact_Icc (a := u) (b := v)
  have hsum {N : ℕ} (hN : (0 : ℝ) < N) (u : ℝ) :
      ∑' n, f n * (indicator (Ico u 1) 1 (n / N)) = ∑ i ∈ .Ico ⌈u * N⌉₊ N, f i := by
    rw [tsum_eq_sum (s := .Ico ⌈u * N⌉₊ N)]
    · apply Finset.sum_congr rfl
      simp +contextual [Nat.ceil_le, le_div_iff₀, div_lt_iff₀, hN]
    · simp +contextual [Nat.ceil_le, le_div_iff₀, div_lt_iff₀, hN]
  rw [tendsto_order]
  refine ⟨fun c _ ↦ ?_, fun c _ ↦ ?_⟩
  · have hg : ∀ᶠ ε in 𝓝[>] (0:ℝ), c < _ := (by fun_prop : ContinuousWithinAt
        (fun ε ↦ A * (1 - 3 * ε)) (Ioi 0) 0) (Ioi_mem_nhds (by grind))
    obtain ⟨ε, hcε, hε, hε'⟩ := (hg.and (Ioc_mem_nhdsGT (by norm_num : (0:ℝ) < 1/3))).exists
    obtain ⟨ψ, h1, h2, h3, -, h5, _, -⟩ := exists_cutoff hε (by linarith : ε < 2 * ε)
      (by linarith) (by linarith : 1 - ε < 1)
    filter_upwards [(tendsto_sum_div_smooth_real h1 h2 h3).comp tendsto_natCast_atTop_atTop
      (Ioi_mem_nhds (by nlinarith [hA]) (a := c)), eventually_gt_atTop 0] with N hN1 _
    have : (0 : ℝ) < N := by norm_cast
    refine hN1.trans_le ?_
    simp only [comp_apply]
    grw [(h5.trans (indicator_le_indicator_of_subset (by grind : Ioo ε 1 ⊆ Ico 0 1) (by simp))) _,
      hsum this, zero_mul, Nat.ceil_zero, Nat.Ico_zero_eq_range]
    exacts [hpos _, WI_summable h2 this, WI_summable (hI zero_lt_one) this]
  · have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ < c := (by fun_prop : ContinuousWithinAt
        (fun ε ↦ A + 2 * C * ε + ε) (Ioi 0) 0) (Iio_mem_nhds (by grind))
    obtain ⟨ε, hcε, hε, hε'⟩ := (hg.and (Ioc_mem_nhdsGT (by norm_num : (0:ℝ) < 1 / 4))).exists
    obtain ⟨ψ, h1, h2, h3, h4, -, -, h7⟩ := exists_cutoff hε (by linarith : ε < 2 * ε)
      (by linarith) (by linarith : 1 < 1 + ε)
    have hcψ : A * ∫ y in Ioi 0, ψ y < c - 2 * C * ε - ε := by nlinarith [hA]
    filter_upwards [(tendsto_sum_div_smooth_real h1 h2 h3).comp tendsto_natCast_atTop_atTop
      (Iio_mem_nhds hcψ), eventually_gt_atTop 0,
      (tendsto_const_div_atTop_nhds_zero_nat C).eventually (gt_mem_nhds hε)] with N hN1 _ hN3
    have hN : (0 : ℝ) < N := by norm_cast
    grw [← Finset.sum_range_add_sum_Ico _ (by rw [Nat.ceil_le]; nlinarith : ⌈2 * ε * (N:ℝ)⌉₊ ≤ N),
      add_div, ← hsum hN, ((indicator_le_indicator_of_subset Ico_subset_Icc_self
      (by simp)).trans h4) _, (by exact hN1 : (∑' n, f n * ψ (n / N)) / N < _),
      le_norm_self (f _), bound, Nat.ceil_lt_add_one, mul_add, add_div, mul_one, hN3]
    · field_simp; grind
    · exact C_nonneg
    · positivity
    exacts [hpos _, WI_summable (hI (by linarith)) hN, WI_summable h2 hN]

end WienerIkehara
