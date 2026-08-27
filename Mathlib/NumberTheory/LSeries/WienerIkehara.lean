/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Alex Kontorovich, Terence Tao, Ruben Van de Velde,
  Arend Mellendijk, Alastair Irving
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

* `WienerIkeharaTheorem'`: the Wiener-Ikehara Tauberian theorem.
* `WeakPNT`: the prime number theorem `∑ n < N, Λ n = N + o(N)` as a consequence.

## Proof outline

Writing `ψ̂` for the Fourier transform, the proof passes through the identities
`∑ f n / n ^ σ * ψ̂ (log (n / x) / (2 * π)) = ∫ F (σ + I * t) * ψ t * x ^ (I * t)` (`first_fourier`)
and its companion for the polar part (`second_fourier`); letting `σ → 1` gives the limiting
Fourier identity (`limiting_fourier`), and the Riemann-Lebesgue lemma turns it into an asymptotic
(`limiting_cor`).  Surjectivity of the Fourier transform on Schwartz space upgrades this to a
smoothed form of the theorem (`wiener_ikehara_smooth`), and non-negativity of `f` together with a
smooth Urysohn lemma replaces the smooth cutoff by the indicator of an interval
(`WienerIkeharaInterval`), whence the theorem.

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


local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n ↦ f n⟩

/-- The data and hypotheses for the Wiener--Ikehara theorem.  Can be conveniently accessed inside
the `WienerIkehara` namespace by adding a `[WienerIkehara]` instance.

The `hf` hypothesis can be derived from `bound`, and `bound` is itself redundant, but implementing
these simplifications is non-trivial, and the hypotheses can usually be verified from existing
API in practice anyway. -/
class WienerIkehara where
  f : ℕ → ℝ
  C : ℝ
  bound : ∀ n, ∑ i ∈ .range n, ‖f i‖ ≤ C * n
  A : ℝ
  G : ℂ → ℂ
  hG : ContinuousOn G {s | 1 ≤ s.re}
  hG' : EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}
  hf : ∀ (σ : ℝ), 1 < σ → LSeriesSummable f σ
  hpos : 0 ≤ f

namespace WienerIkehara

private abbrev c₀ := π⁻¹ * 2⁻¹

section FourierIdentities

private def statistic₁ [WienerIkehara] (σ : ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n, term f σ n * φ (c₀ * log (n / x))

private def statistic₂ [WienerIkehara] (σ : ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  A * ↑(x ^ (1 - σ)) * ∫ u in Ici (- log x), rexp (-u * (σ - 1)) * φ (c₀ * u)

/-- A key statistic in the Wiener--Ikehara analysis involving an exponent `σ`, a test
function `φ`, and a scale parameter `x`. -/
private def statistic [WienerIkehara] (σ : ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  statistic₁ σ φ x - statistic₂ σ φ x

variable {x σ : ℝ} {ψ : ℝ → ℂ}

private lemma sum_term_mul_fourier_eq [WienerIkehara] (hsupp : Integrable ψ) (hx : 0 < x)
    (hσ : 1 < σ) : statistic₁ σ (𝓕 ψ) x =
    ∫ t : ℝ, LSeries f (σ + t * I) * ψ t * x ^ (t * I) :=
  calc
    _ = ∑' n, ∫ t, term f σ n * 𝐞 (-(t * (c₀ * log (n / x)))) • ψ t := by
      simp [statistic₁, fourier_eq, RCLike.inner_apply', -RCLike.inner_apply, integral_const_mul]
    _ = ∫ t, ∑' n, term f σ n * 𝐞 (-(t * (c₀ * log (n / x)))) • ψ t := by
      refine (integral_tsum (by fun_prop) ?_).symm
      have (n : ℕ) : AEMeasurable fun u ↦
        (‖fourierChar (-(u * (c₀ * (n / x).log))) • ψ u‖ₑ : ENNReal) := by fun_prop
      simp_rw [enorm_mul, lintegral_const_mul'' _ (this _)]
      have : (∑' (i : ℕ), (‖term f (↑σ) i‖₊ : ENNReal)) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ≠ ⊤ := by
        refine ENNReal.mul_ne_top ?_ (ne_top_of_lt hsupp.2)
        simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal,
          NNReal.summable_coe, (hf σ hσ).norm.toNNReal]
      simp_all [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
    _ = _ := by
      congr with y
      rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries,
        ← Summable.tsum_smul_const]
      · congr with n
        by_cases hn : n = 0
        · simp [*]
        suffices cexp (-(2 * π * (y * ((π : ℂ)⁻¹ * 2⁻¹ * log (n / x))) * I))
          = x ^ (y * I) / n ^ (y * I) by
          simp [Circle.smul_def, fourierChar_apply, hn, cpow_add, field, this]
        simp [cpow_def_of_ne_zero, hx.ne.symm, hn, ← Complex.exp_sub, log_div, ofReal_log, hx.le]
        congr
        field_simp
        grind
      · exact (hf σ hσ).of_re_le_re (by simp)

private lemma integral_exp_mul_fourier_eq [WienerIkehara] (hcont : Measurable ψ)
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ) : statistic₂ σ (𝓕 ψ) x =
    A * ∫ t, (1 / (σ + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by
  unfold statistic₂; rw [mul_assoc]; congr 1
  calc
  _ = ↑(x ^ (1 - σ)) * ∫ u in Ici (-log x),
      ∫ a, (rexp (-u * (σ - 1)) : ℂ) • 𝐞 (-(a * (c₀ * u))) • ψ a := by
    simp_rw [fourier_real_eq, ← smul_eq_mul, ← integral_smul]
  _ = ↑(x ^ (1 - σ)) * ∫ a, ∫ u in _, _ := by
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-log x))).prod volume
    congr 1
    suffices Integrable (uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ - 1))) : ℂ) •
      (𝐞 (-(a * (c₀ * u))) : ℂ) • ψ a) ν from integral_integral_swap this
    refine ⟨ by fun_prop, ?_ ⟩
    let f1 := fun (a1 : ℝ) ↦ ‖cexp (-(a1 * (σ - 1)))‖ₑ
    let f2 := (‖ψ ·‖ₑ)
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, uncurry]
    apply (lintegral_prod_mul (by fun_prop) (by fun_prop)).trans_lt
    suffices IntegrableOn (fun (x : ℝ) ↦ cexp (-(x * (σ - 1)))) (Ici (-log x)) from
      ENNReal.mul_lt_top this.2 hsupp.2
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
        rw [ofReal_cpow hx.le, ofReal_sub, ← cpow_add _ _ this, ofReal_one]
        ring_nf
        simp

/-- The main result of this section: an initial Fourier identity expressing a statistic of
`f` as an error term of Fourier integral type. -/
private lemma sum_term_mul_sub_mul_integral_eq [WienerIkehara]
    (hψ1 : Continuous ψ) (hψ2 : HasCompactSupport ψ) (hx : 1 ≤ x) (σ : ℝ) (hσ : 1 < σ) :
    statistic σ (𝓕 ψ) x = ∫ t : ℝ, G (σ + t * I) * ψ t * x ^ (t * I) := by
  have hx' : 0 < x := by linarith
  have : Integrable ψ := hψ1.integrable_of_hasCompactSupport hψ2
  simp_rw [statistic, sum_term_mul_fourier_eq this hx' hσ,
    integral_exp_mul_fourier_eq hψ1.measurable this hx' hσ]
  have (u : ℝ) : σ + u * I - 1 ≠ 0 := by
    intro h; have := congr_arg re h; simp at this; linarith
  have : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (by fun_prop) (by simp [hx'])
  rw [← integral_const_mul, ← integral_sub]
  · refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
    simp_rw [hG' (by simp [hσ] : 1 < (σ + u * I).re)]
    field_simp
  · have : Continuous fun x : ℝ ↦ LSeries f (σ + x * I) := by
      refine continuous_tsum (fun i ↦ ?_) (hf _ hσ).norm (by simp [norm_term_eq])
      by_cases h : i = 0
      · simpa [h] using continuous_const
      · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
          (by simp [h])
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hψ2.mul_left.mul_right
  · apply Continuous.integrable_of_hasCompactSupport (by fun_prop) hψ2.mul_left.mul_right.mul_left

end FourierIdentities

section HelperFunctions

variable {a c t x : ℝ}

private def F₂ (t : ℝ) : ℝ := (t * (1 + (c₀ * log t) ^ 2))⁻¹

private def F₄ (x i : ℝ) : ℝ := 1 / i * (1 + (c₀ * log (i / x)) ^ 2)⁻¹

private lemma F₂_nonneg (ht : 0 ≤ t) : 0 ≤ F₂ t := by dsimp only [F₂]; positivity

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

private lemma F₄_of_F₂ (hx : x ≠ 0) (i : ℝ) : F₄ x i = x⁻¹ * F₂ (i / x) := by
  unfold F₄ F₂; field_simp

private lemma F₄_le_one (i : ℕ) : F₄ x i ≤ 1 := by
  unfold F₄
  by_cases hi : i = 0
  · simp [hi]
  grw [← sq_nonneg, ← (mod_cast by omega : 1 ≤ (i : ℝ))]
  simp

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

private abbrev C₀ := 1 + ∫ t in Ioi 0, F₂ t

private lemma C₀_nonneg : 0 ≤ C₀ :=
  add_nonneg zero_le_one (setIntegral_nonneg measurableSet_Ioi (fun _ hx ↦ F₂_nonneg hx.le))

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

variable {x : ℝ} {ψ : ℝ → ℂ} (Ψ : 𝓢(ℝ, ℂ))

private lemma bound_sum_log_range [WienerIkehara] (hx : 1 ≤ x) (n : ℕ) :
    ∑ i ∈ .range n, ‖f i‖ / i * (1 + (c₀ * log (i / x)) ^ 2)⁻¹ ≤ C * C₀ := by
  let F₅ (i : ℕ) : ℝ := if i = 0 then 1 else F₄ x i
  have l0 : x ≠ 0 := by linarith
  have l3 : 0 ≤ C := (norm_nonneg (f 0)).trans (by simpa using bound 1)
  refine (Finset.sum_le_sum (g := fun i ↦ ‖f i‖ * F₅ i) (fun i _ ↦ ?_)).trans ?_
  · by_cases hi : i = 0 <;> simp [F₄, hi, F₅, field]
  trans C * ∑ i ∈ .range n, F₅ i
  · have l1 i : 0 ≤ F₅ i := by
      by_cases hi : i = 0 <;> simp only [F₄, hi, ↓reduceIte, zero_le_one, F₅]; positivity
    have l2 : Antitone F₅ := by
      intro i j hij; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
        simp only [hj, ↓reduceIte, hi, le_refl, F₅]
      · exact F₄_le_one _
      · omega
      · simp only [F₄_of_F₂ l0]
        gcongr
        apply F₂_antitone
        · simp only [mem_Ioi]; positivity
        · simp only [mem_Ioi]; positivity
        · gcongr
    simpa [← Finset.mul_sum] using Finset.sum_mul_le_sum_mul_of_sum_range_le
      (c := fun _ ↦ C) (fun k _ ↦ by simpa [mul_comm] using bound k) l1 l2
  gcongr; simp only [F₄_of_F₂ l0, F₅]
  by_cases h : n = 0
  · simp only [h, Finset.range_zero, Finset.sum_empty, C₀_nonneg]
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
  rw [intervalIntegral.integral_comp_div (x⁻¹ * F₂ ·) l0]
  simp only [intervalIntegral.integral_const_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, this, ↓reduceIte, uIoc_of_le,
    smul_eq_mul, one_mul, zero_div, mul_inv_cancel₀ l0, ← mul_assoc]
  apply integral_mono_measure
  · exact Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · exact eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
      fun x hx ↦ F₂_nonneg hx.le
  · simpa using! (F₂_integrable (a := 1) zero_lt_one).mono_set Ioi_subset_Ici_self

private lemma summable_sum_log_range [WienerIkehara] (hx : 1 ≤ x) :
  Summable fun n ↦ ‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹ :=
    summable_of_sum_range_le (fun _ ↦ by positivity)
    (fun n ↦ by simpa using bound_sum_log_range hx n)

private theorem limiting_fourier_lim1 [WienerIkehara] (hx : 1 ≤ x) :
    Tendsto (fun σ : ℝ ↦ statistic₁ σ (𝓕 Ψ : 𝓢(ℝ, ℂ)) x) (𝓝[>] 1)
      (𝓝 (statistic₁ 1 (𝓕 Ψ : 𝓢(ℝ, ℂ)) x)) := by
  unfold statistic₁
  refine tendsto_tsum_of_dominated_convergence ((summable_sum_log_range hx).mul_left Ψ.Q)
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
    have : 1 ≤ (n : ℝ) := mod_cast (by omega)
    have := Ψ.Q_nonneg
    grw [Ψ.decay_bound, ← hσ]
    simp; grind

private theorem limiting_fourier_lim2 [WienerIkehara] (hx : 1 ≤ x) :
    Tendsto (fun σ ↦ statistic₂ σ (𝓕 Ψ : 𝓢(ℝ, ℂ)) x) (𝓝[>] 1)
      (𝓝 (statistic₂ 1 (𝓕 Ψ : 𝓢(ℝ, ℂ)) x)) := by
  apply Tendsto.mul
  · suffices Tendsto (fun σ : ℝ ↦ ofReal (x ^ (1 - σ))) (𝓝[>] 1) (𝓝 1) by
      simpa using this.const_mul ↑A
    suffices Tendsto (fun σ : ℝ ↦ x ^ (1 - σ)) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp this
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
      simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
        neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
        sub_zero]
      trans rexp (log x * (σ - 1))
      ·  apply exp_monotone
         simpa using neg_le_neg (mul_le_mul_of_nonneg_right ht (by linarith))
      have : σ - 1 ≤ 1 := by linarith
      refine (exp_monotone (mul_le_mul_of_nonneg_left this (log_nonneg hx))).trans ?_
      simpa using by grind [Real.exp_log, abs_of_nonneg]
  · refine Eventually.of_forall fun x ↦ ?_
    suffices Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
      simpa using this.mul_const _
    apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
    suffices Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using this.tendsto 1
    continuity

private theorem limiting_fourier_lim3 [WienerIkehara]
    {Ψ : 𝓢(ℝ, ℂ)} (hΨ : HasCompactSupport Ψ) (hx : 1 ≤ x) :
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

set_option backward.isDefEq.respectTransparency false in
private lemma limiting_cor_aux : Tendsto (fun x : ℝ ↦ ∫ t, ψ t * x ^ (t * I)) atTop (𝓝 0) := by
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

private lemma limiting_cor [WienerIkehara] {Ψ : 𝓢(ℝ, ℂ)} (hΨ : HasCompactSupport Ψ) :
    Tendsto (statistic 1 (𝓕 Ψ : 𝓢(ℝ, ℂ))) atTop (𝓝 0) := by
  apply (limiting_cor_aux (ψ := fun t ↦ G (1 + t * I) * (Ψ t))).congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  unfold statistic
  apply (tendsto_nhds_unique_of_eventuallyEq ((limiting_fourier_lim1 Ψ (by linarith)).sub
    (limiting_fourier_lim2 Ψ hx)) (limiting_fourier_lim3 hΨ hx) _).symm
  simpa [eventuallyEq_nhdsWithin_iff] using!
    Eventually.of_forall (sum_term_mul_sub_mul_integral_eq Ψ.continuous hΨ hx)

end LimitingFourierIdentity

section LimitingFourierIdentitySchwartz

variable {x : ℝ} (Ψ : 𝓢(ℝ, ℂ))

private lemma summable_fourier_aux (x) (f : ℕ → ℂ) (n) :
    ‖(term f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ ≤
      Ψ.Q * (‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (Ψ.decay_bound (1 / (2 * π) * log (n / x)))
    (norm_nonneg (f n / n)) using 1
  · by_cases h : n = 0 <;> simp [term, h]
  · simp; grind

private lemma summable_fourier [WienerIkehara] (hx : 1 ≤ x) :
    Summable fun n ↦ ‖(term f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (summable_fourier_aux Ψ x f)
    (by simpa using (summable_sum_log_range hx).const_smul Ψ.Q)

private lemma bound_I1 [WienerIkehara] (hx : 1 ≤ x) :
    ‖statistic₁ 1 (𝓕 Ψ : 𝓢(ℝ, ℂ)) x‖ ≤
    Ψ.Q • ∑' n, ‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹ := by
  have l5 : Summable fun n ↦ ‖f n‖ / n * ((1 + (c₀ * (log (n / x))) ^ 2)⁻¹) := by
    simpa using summable_sum_log_range hx
  have l1 : Summable fun n ↦ ‖(term f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ :=
    summable_fourier Ψ hx
  unfold statistic₁
  apply (norm_tsum_le_tsum_norm l1).trans
  grw [Summable.tsum_mono l1 (by simpa using l5.const_smul Ψ.Q) (summable_fourier_aux Ψ x f)
    , ← Summable.tsum_const_smul _ l5]
  simp

private lemma bound_I1' [WienerIkehara] (hx : 1 ≤ x) :
    ‖statistic₁ 1 (𝓕 Ψ : 𝓢(ℝ, ℂ)) x‖ ≤ Ψ.Q * C * C₀ := by
  grw [bound_I1 Ψ hx, smul_eq_mul, mul_assoc]
  refine mul_le_mul le_rfl ?_ (tsum_nonneg (fun _ ↦ by positivity)) Ψ.Q_nonneg
  calc
    _ ≤ _ := tsum_le_of_sum_range_le (fun _ ↦ by positivity) (bound_sum_log_range hx)
    _ = _ := by congr

private lemma bound_I2 (x : ℝ) :
    ‖∫ u in Ici (-log x), 𝓕 Ψ (c₀ * u)‖ ≤ Ψ.Q * (2 * π ^ 2) := by
  have key a : ‖𝓕 Ψ (c₀ * a)‖ ≤ Ψ.Q * (1 + (c₀ * a) ^ 2)⁻¹ := Ψ.decay_bound _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (c₀ * a) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (by positivity)
  have := (𝓕 Ψ).continuous
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (c₀ * a) ^ 2)⁻¹ :=
    Eventually.of_forall fun _ ↦ by positivity
  refine (norm_integral_le_integral_norm _).trans <|
    (setIntegral_mono ((l3.const_mul Ψ.Q).mono' (by fun_prop) (by simp [key])).integrableOn
      (l3.const_mul _).integrableOn key).trans ?_
  rw [integral_const_mul]; gcongr
  · apply Q_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_mul_left (fun x ↦ (1 + x ^ 2)⁻¹)]
  simp [abs_eq_self.mpr twopi]; grind

private lemma bound_main [WienerIkehara] (hx : 1 ≤ x) :
    ‖statistic 1 (𝓕 Ψ : 𝓢(ℝ, ℂ)) x‖ ≤ Ψ.Q * (C * C₀ + |A| * (2 * π ^ 2)) := by
  unfold statistic statistic₂
  grw [norm_sub_le, bound_I1' _ hx, norm_mul]
  simp only [sub_self, rpow_zero, ofReal_one, mul_one, norm_real, norm_eq_abs, mul_zero,
    Real.exp_zero, one_mul]
  grw [bound_I2 Ψ x]
  grind

private lemma limiting_cor_schwartz [WienerIkehara] :
    Tendsto (statistic 1 (𝓕 Ψ : 𝓢(ℝ, ℂ))) atTop (𝓝 0) := by
  have hC : 0 ≤ C := by
    have h1 : ‖f 0‖ ≤ C := by simpa using bound 1
    linarith [norm_nonneg (f 0)]
  simp_rw [Metric.tendsto_nhds]; intro ε hε
  let M := C * C₀ + |A| * (2 * π ^ 2)
  have hM : 0 < 1 + M := by positivity [C₀_nonneg]
  obtain ⟨φ, hφcs, hφQ⟩ : ∃ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) ∧
      (Ψ - φ).Q < (ε / 2) / (1 + M) := by
    have hcont : Continuous fun φ : 𝓢(ℝ, ℂ) ↦ (Ψ - φ).Q :=
      SchwartzMap.Q_continuous.comp (continuous_const.sub continuous_id)
    have hψmem : Ψ ∈ {φ : 𝓢(ℝ, ℂ) | (Ψ - φ).Q < (ε / 2) / (1 + M)} := by
      change (Ψ - Ψ).Q < (ε / 2) / (1 + M)
      rw [show (Ψ - Ψ).Q = 0 by simp [sub_self, Q, _root_.map_zero]]; positivity
    obtain ⟨φ, hφcs, hφQ⟩ := SchwartzMap.dense_hasCompactSupport.inter_open_nonempty _
      (isOpen_lt hcont continuous_const) ⟨Ψ, hψmem⟩
    exact ⟨φ, hφQ, hφcs⟩
  have key := limiting_cor hφcs
  simp_rw [Metric.tendsto_nhds, dist_zero_right] at key
  filter_upwards [eventually_ge_atTop 1, key (ε / 2) (by positivity)] with x hx keyx
  have hFsub (t : ℝ) : 𝓕 (Ψ - φ) t = 𝓕 Ψ t - 𝓕 φ t := by
    have h : 𝓕 (Ψ - φ) t = (fourierTransformCLM ℂ (Ψ - φ)) t := rfl
    rw [h, map_sub, sub_apply]; rfl
  have hsummψ : Summable fun n : ℕ ↦ (term f 1 n) * 𝓕 Ψ (c₀ * log (↑n / x)) := by
    have h := summable_fourier Ψ hx; rwa [summable_norm_iff] at h
  have hsummφ : Summable fun n : ℕ ↦ (term f 1 n) * 𝓕 φ (c₀ * log (↑n / x)) := by
    have h := summable_fourier φ hx; rwa [summable_norm_iff] at h
  have S1_sub : statistic₁ 1 (𝓕 (Ψ - φ) : 𝓢(ℝ, ℂ)) x = statistic₁ 1 (𝓕 Ψ : 𝓢(ℝ, ℂ)) x -
    statistic₁ 1 (𝓕 φ : 𝓢(ℝ, ℂ)) x := by
    simp only [statistic₁]; rw [ofReal_one, ← hsummψ.tsum_sub hsummφ]
    exact tsum_congr fun n ↦ by rw [hFsub]; ring
  have S2_sub : statistic₂ 1 (𝓕 (Ψ - φ) : 𝓢(ℝ, ℂ)) x = statistic₂ 1 (𝓕 Ψ : 𝓢(ℝ, ℂ)) x -
    statistic₂ 1 (𝓕 φ : 𝓢(ℝ, ℂ)) x := by
    simp only [statistic₂, sub_self, rpow_zero, ofReal_one, mul_one, mul_zero, Real.exp_zero,
      one_mul]
    rw [← mul_sub, ← integral_sub]
    · congr 1
      exact setIntegral_congr_fun measurableSet_Ici fun _ _ ↦ hFsub _
    · exact ((𝓕 Ψ).integrable.comp_mul_left' (by positivity)).restrict
    · exact ((𝓕 φ).integrable.comp_mul_left' (by positivity)).restrict
  have : statistic 1 (𝓕 Ψ : 𝓢(ℝ, ℂ)) x = statistic 1 (𝓕 (Ψ - φ) : 𝓢(ℝ, ℂ)) x
    + statistic 1 (𝓕 φ : 𝓢(ℝ, ℂ)) x := by unfold statistic; grind
  have : ‖statistic 1 (𝓕 (Ψ - φ) : 𝓢(ℝ, ℂ)) x‖ < ε / 2 := by
    have hb : ‖statistic 1 (𝓕 (Ψ - φ) : 𝓢(ℝ, ℂ)) x‖ ≤ (Ψ - φ).Q * M := bound_main (Ψ - φ) hx
    apply hb.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp)
      (by positivity [C₀_nonneg]) (Q_nonneg _)).trans_lt
    convert! (mul_lt_mul_iff_left₀ hM).mpr hφQ using 1; field_simp
  grind [dist_zero_right, norm_add_le]

end LimitingFourierIdentitySchwartz
section Smooth

variable {ψ Ψ : ℝ → ℂ}

private lemma comp_exp_support0 (hplus : closure (support ψ) ⊆ Ioi 0) : ∀ᶠ x in 𝓝 0, ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ lt_irrefl 0 <| mem_Ioi.mp (hplus h))

private theorem comp_exp_support (hsupp : HasCompactSupport ψ)
    (hplus : closure (support ψ) ⊆ Ioi 0) : HasCompactSupport (ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp ⊢
  exact ⟨tendsto_exp_atBot <| comp_exp_support0 hplus, tendsto_exp_atTop hsupp.2⟩

private lemma wiener_ikehara_smooth_aux (l0 : Continuous ψ) (hsupp : HasCompactSupport ψ)
    (hplus : closure (support ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ u in Ioi (-log x), ↑(rexp u) * ψ (rexp u) = ∫ y in Ioi (1 / x), ψ y := by
  have : HasCompactSupport (rexp • (ψ ∘ rexp)) := (comp_exp_support hsupp hplus).smul_left
  have : IntegrableOn (fun x ↦ rexp x • (ψ ∘ rexp) x) (Ici (-log x)) volume :=
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) this).integrableOn
  simpa [Real.exp_neg, exp_log hx] using integral_deriv_smul_comp_Ioi (by fun_prop)
    tendsto_exp_atTop (fun t _ ↦ (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (by fun_prop) (l0.integrable_of_hasCompactSupport hsupp).integrableOn this

private theorem wiener_ikehara_smooth_sub [WienerIkehara] (h1 : Integrable ψ)
    (hplus : closure (support ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (A * ∫ (y : ℝ) in Ioi x⁻¹, ψ y) - A * ∫ (y : ℝ) in Ioi 0, ψ y)
      atTop (𝓝 0) := by
  obtain ⟨ε, _, _⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq; filter_upwards [eventually_gt_atTop ε⁻¹] with x _
  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub,
    ← integral_sub (h1.indicator measurableSet_Ioi) (h1.indicator measurableSet_Ioi)]
  simp only [mul_eq_zero, ofReal_eq_zero]
  refine Or.inr (integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_))
  have : 0 < ε⁻¹ := by positivity
  have : 0 < x := by linarith
  have : 0 < x⁻¹ := by positivity
  rw [(by grind : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹), indicator_union_of_disjoint (by simp) ψ]
  simp only [Pi.zero_apply]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · grind [abs_le, norm_eq_abs, dist_zero_right, indicator_of_mem, inv_lt_comm₀]
  simp [ht]

private lemma wiener_ikehara_smooth [WienerIkehara] (hsmooth : ContDiff ℝ ∞ ψ)
    (hsupp : HasCompactSupport ψ) (hplus : closure (support ψ) ⊆ Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * ψ (n / x)) / x - A * ∫ y in Ioi 0, ψ y)
      atTop (𝓝 0) := by
  let h (x : ℝ) : ℂ := rexp (2 * π * x) * ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (ofRealCLM.contDiff.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = h2.toSchwartzMap h1 :=
    ⟨𝓕⁻ _, fourier_fourierInv_eq _⟩
  have l1 {y} (hy : 0 < y) : y * ψ y = 𝓕 g (c₀ * log y) := by
    simp only [hg, HasCompactSupport.toSchwartzMap_toFun, ofReal_exp,
      ofReal_mul, ofReal_ofNat, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]
  have key := limiting_cor_schwartz g
  have l2 : ∀ᶠ x in atTop, statistic₁ 1 (𝓕 g : 𝓢(ℝ, ℂ)) x =
      ∑' (n : ℕ), f n * ψ (n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    unfold statistic₁
    congr; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp [ofReal_div, ofReal_natCast, term, hn]
    field_simp
  have l3 : ∀ᶠ x in atTop, statistic₂ 1 (𝓕 g : 𝓢(ℝ, ℂ)) x =
      A * ∫ (y : ℝ) in Ioi x⁻¹, ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [statistic₂, hg, HasCompactSupport.toSchwartzMap_toFun, h]
    field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    left
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx
  have l4 : Tendsto (fun x => (A * ∫ (y : ℝ) in Ioi x⁻¹, ψ y) - A * ∫ (y : ℝ) in Ioi 0, ψ y)
      atTop (𝓝 0) :=
    wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus
  unfold statistic at key
  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4

private lemma wiener_ikehara_smooth_real [WienerIkehara] {Ψ : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : closure (support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Ioi 0, Ψ y)) := by
  have : Tendsto (fun x ↦ (∑' n, f n * (ofReal ∘ Ψ) (n / x)) / x) atTop
      (nhds (A * ∫ y in Ioi 0, (ofReal ∘ Ψ) y)) := tendsto_sub_nhds_zero_iff.mp <|
      wiener_ikehara_smooth (ofRealCLM.contDiff.comp hsmooth) (hsupp.comp_left rfl)
      (by rwa [support_comp_eq]; simp)
  have := (continuous_re.tendsto _).comp this
  simp at this; norm_cast at this

end Smooth

section Interval

variable {a b c d x : ℝ}

/-- A smooth Urysohn lemma on the real line: for `a < b` and `c < d` there is a smooth compactly
supported function squeezed between the indicators of `Icc b c` and `Ioo a d`, whose support is
exactly `Ioo a d`.  This specializes `exists_contMDiff_support_eq_eq_one_iff`. -/
lemma exists_contDiff_one_on_Icc_support_eq_Ioo (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      indicator (Icc b c) 1 ≤ Ψ ∧ Ψ ≤ indicator (Ioo a d) 1 ∧ support Ψ = Ioo a d := by
  obtain ⟨Ψ, hsmooth, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := modelWithCornersSelf ℝ ℝ) (n := ⊤)
      isOpen_Ioo isClosed_Icc (Icc_subset_Ioo h1 h3)
  refine ⟨Ψ, hsmooth.contDiff, ?_, indicator_le' (fun x hx ↦ ?_) (fun x _ ↦ ?_),
    fun x ↦ le_indicator_apply (fun _ ↦ ?_) (fun hx ↦ ?_), hsupp⟩
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc (hsupp ▸ Ioo_subset_Icc_self)
  · exact ((hone x).mp hx).ge
  · exact (hrange (mem_range_self x)).1
  · exact (hrange (mem_range_self x)).2
  · have hx' : x ∉ support Ψ := hsupp ▸ hx
    simp only [mem_support, not_not] at hx'
    exact hx'.le

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (support ψ) ⊆ Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by
  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := exists_contDiff_one_on_Icc_support_eq_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      by grind
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (support ψ) ⊆ Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by
  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := exists_contDiff_one_on_Icc_support_eq_Ioo
    (by linarith : a - ε / 2 < a) (by linarith : b < b + ε / 2)
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by grind -- intro t ht; simp at ht ⊢; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable [WienerIkehara] {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n ↦ f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold HasFiniteSupport
  simp only [support_mul]; apply Finite.inter_of_right; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le [WienerIkehara] {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le [WienerIkehara] (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) :
      f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := bound ⌈b * x⌉₊; simp only [norm_eq_abs] at this; apply this.trans
  have : 0 ≤ C := by have := bound 1; simp only [Finset.range_one,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' [WienerIkehara] (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hb hx

lemma le_of_eventually_nhdsWithin (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b :=
  ge_of_tendsto (tendsto_id.mono_left nhdsWithin_le_nhds) h

lemma ge_of_eventually_nhdsWithin (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a :=
  le_of_tendsto (tendsto_id.mono_left nhdsWithin_le_nhds) h

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (· / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  convert ContinuousWithinAt.tendsto_nhdsWithin _ _
  · grind
  · fun_prop
  · intro _ _; simp_all; field_simp; linarith

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto ((b - a) - · / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  convert ContinuousWithinAt.tendsto_nhdsWithin _ _
  · grind
  · fun_prop
  · intro _ _; simp_all; field_simp; linarith

theorem residue_nonneg [WienerIkehara] : 0 ≤ A := by
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have l2 : 0 ≤ ψ := le_trans (indicator_nonneg (by simp)) h4
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have : Ico 1 2 ⊆ support ψ := by intro x _; have := h4 x; simp_all; linarith
    have : 1 ≤ volume (support ψ ∩ Ioi 0) := by
      convert! volume.mono (by grind : Ico 1 2 ⊆ support ψ ∩ Ioi 0); norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall l2)
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn] using
      zero_lt_one.trans_le this
  have := div_nonneg (ge_of_tendsto (wiener_ikehara_smooth_real h1 h2 h3)
    ?_) l4.le
  · field_simp at this; exact this
  · filter_upwards [eventually_ge_atTop 0] with x hx using
      div_nonneg (tsum_nonneg (fun _ ↦ mul_nonneg (hpos _) (l2 _))) hx

lemma WienerIkeharaInterval [WienerIkehara] (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop
      (nhds (A * (b - a))) := by
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab; clear hab
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx using
      div_nonneg (tsum_nonneg (fun _ ↦ mul_nonneg (hpos _) (hg _))) hx
  have hA : 0 ≤ A := residue_nonneg
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by
    simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) :=
    ⟨C * 2 * b, WI_sum_Iab_le' (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le
  have : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans; rw [l1.limsup_eq]; gcongr
    obtain h | h := eq_or_ne A 0
    · simpa [h] using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx
  have : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3; rw [l1.liminf_eq]; gcongr
    obtain h | h := eq_or_ne A 0
    · simpa [h] using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx
  grind [tendsto_of_liminf_eq_limsup, liminf_le_limsup]

end Interval

variable {n : ℕ} {a b x : ℝ}

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  simp [Nat.ceil_le, Nat.lt_ceil, le_div_iff₀, div_lt_iff₀, hx]

lemma tsum_indicator [WienerIkehara] (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ .Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  rw [tsum_eq_sum]
  · apply Finset.sum_congr rfl
    simp +contextual [mem_Ico_iff_div hx]
  · simp +contextual [mem_Ico_iff_div hx]

lemma WienerIkeharaInterval_discrete [WienerIkehara] (ha : 0 < a)
    (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ .Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop
      (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' [WienerIkehara] (ha : 0 < a)
    (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop
      (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete ha hb |>.comp tendsto_natCast_atTop_atTop

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  apply squeeze_zero' (g := fun p : ℝ × ℕ => p.1 + 1 / p.2)
  · apply Filter.Eventually.of_forall
    intro x; positivity
  · filter_upwards [eventually_mem_nhdsWithin.prod_inl atTop,
      (eventually_gt_atTop (0 : ℕ)).prod_inr _] with p hp hn
    simp at hp; field_simp
    apply (Nat.ceil_lt_add_one _).le; positivity
  · rw [nhdsWithin]
    simpa using (Filter.tendsto_fst.mono_right inf_le_left).add
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp Filter.tendsto_snd)

def S [WienerIkehara] (ε : ℝ) (N : ℕ) : ℝ := (∑ n ∈ .Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S [WienerIkehara] {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) :
    S 0 N - S ε N = (∑ i ∈ .range ⌈ε * N⌉₊, f i) / N := by
  have : ⌈ε * N⌉₊ ≤ N := by
    rw [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = .range ⌈ε * N⌉₊ ∪ .Ico ⌈ε * N⌉₊ N := by grind
  have r2 : Disjoint (.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico]; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, add_div]

lemma tendsto_S_S_zero [WienerIkehara] :
    TendstoUniformlyOnFilter S (S 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff]; intro δ hδ
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1; exact r1 (Iio_mem_nhds hδ)
  filter_upwards [l1, Eventually.prod_inl (inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)) _]
    with (ε, N) h1 h2
  suffices ‖(∑ i ∈ .range ⌈ε * ↑N⌉₊, f i) / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N by
    simpa [← S_sub_S h2.2] using! this.trans_lt h1
  have r1 := bound ⌈ε * N⌉₊
  have r2 : 0 ≤ ∑ i ∈ .range ⌈ε * N⌉₊, f i := Finset.sum_nonneg (fun i _ ↦ hpos i)
  simp only [norm_of_nonneg (hpos _), norm_div,
    norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
  grw [r1]

/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/
theorem WienerIkeharaTheorem [WienerIkehara] :
    Tendsto (fun N ↦ (∑ i ∈ .range N, f i) / N) atTop (𝓝 A) := by
  convert_to Tendsto (S 0) atTop (𝓝 A); · ext N; simp [S]
  apply tendsto_S_S_zero.tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hε.1 hε.2
  · convert ContinuousWithinAt.tendsto _
    · simp
    fun_prop

end WienerIkehara

theorem WeakPNT : Tendsto (fun N ↦ (∑ i ∈ Finset.range N, Λ i) / N) atTop (𝓝 1) := by
  let data : WienerIkehara := {
    f := Λ
    C := log 4 + 4
    bound N := by
      by_cases! h : N = 0
      · simp [h]
      simp only [norm_eq_abs]
      rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
      simp_rw [abs_of_nonneg vonMangoldt_nonneg]
      rw [← Chebyshev.psi_eq_sum_Icc]
      grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
      gcongr
      linarith
    A := 1
    G := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
    hG := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
    hG' s hs := by
      simp only [mem_ofPred_eq, ofReal_one, one_div] at hs ⊢
      have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
      simp only [this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div,
        sub_left_inj]
      apply LSeries_congr
      intro n _
      simp only [ofReal_inj, indicator_apply_eq_self, mem_ofPred_eq]
      exact absurd (Subsingleton.eq_one _)
    hf σ hσ := LSeriesSummable_vonMangoldt (s := σ) hσ
    hpos := by intro; simp
  }
  exact data.WienerIkeharaTheorem
