/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Alex Kontorovich, Terence Tao, Ruben Van de Velde,
  Arend Mellendijk, Alastair Irving
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Compactly supported `Cⁿ` functions and the Sobolev space `W^{2,1}`

Auxiliary spaces used in the proof of the Wiener-Ikehara Tauberian theorem: `CS n E` is the
space of `Cⁿ` functions `ℝ → E` with compact support, and `W1 n E` (with `W21 = W1 2 ℂ`) is the
space of `Cⁿ` functions all of whose derivatives up to order `n` are integrable.

This file is a draft port from the `PrimeNumberTheoremAnd` project.
-/

@[expose] public section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap BigOperators
  FourierTransform
open scoped ContDiff

@[continuity, fun_prop]
lemma continuous_FourierIntegral {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp [RCLike.inner_apply', -RCLike.inner_apply, continuous_mul])
    hf

/-- `f` lies in the Sobolev space `W^{2,1}(ℝ)`: it is `C²`, and it and its first two
derivatives are integrable.  This is a `Prop`-valued replacement for the bundled space `W21`. -/
structure IsW21 (f : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ 2 f
  integrable' : ∀ ⦃k⦄, k ≤ 2 → Integrable (iteratedDeriv k f)

namespace W21

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun _ ↦ by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun _ ↦ by simp)))

end W21

@[fun_prop]
lemma integrable_iteratedDeriv_Schwarz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : 𝓢(ℝ, E)} {n : ℕ} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := f.derivCLM ℝ E)

namespace IsW21

variable {f g : ℝ → ℂ}

@[fun_prop]
lemma integrable (h : IsW21 f) : Integrable f := by
  simpa using h.integrable' zero_le_two

@[fun_prop]
lemma integrable_deriv (h : IsW21 f) : Integrable (deriv f) := by
  simpa using h.integrable' one_le_two

@[fun_prop]
lemma integrable_deriv_deriv (h : IsW21 f) : Integrable (deriv (deriv f)) := by
  simpa [iteratedDeriv_succ] using h.integrable' le_rfl

lemma sub (hf : IsW21 f) (hg : IsW21 g) : IsW21 (f - g) where
  smooth := hf.smooth.sub hg.smooth
  integrable' k hk := by
    convert (hf.integrable' hk).sub (hg.integrable' hk)
    ext
    exact iteratedDeriv_sub (hf.smooth.of_le (by simp [hk])).contDiffAt
      (hg.smooth.of_le (by simp [hk])).contDiffAt

lemma decay_bounds_key (hf : IsW21 f) (u : ℝ) :
    ‖𝓕 f u‖ ≤ W21.norm f * (1 + u ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + u ^ 2), mul_comm]
  simpa [W21.norm, iteratedDeriv_succ] using
    one_add_sq_mul_norm_fourier_le hf.smooth hf.integrable' u

lemma integrable_fourier (hf : IsW21 f) {c : ℝ} (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 f (u / c) := by
  apply Integrable.mono' (g := fun u => (W21.norm f) / (1 + (u / c) ^ 2)) ?_ (by fun_prop) ?_
  · simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul (W21.norm f)
  · exact Eventually.of_forall (fun _ ↦ decay_bounds_key hf _)

end IsW21

lemma isW21_of_hasCompactSupport {f : ℝ → ℂ} (h1 : ContDiff ℝ 2 f) (h2 : HasCompactSupport f) :
    IsW21 f := by
  refine ⟨h1, fun k hk ↦ ?_⟩; match k with
  | 0 => exact h1.continuous.integrable_of_hasCompactSupport h2
  | 1 => simpa using (h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport h2.deriv.deriv

lemma isW21_of_schwartz (f : 𝓢(ℝ, ℂ)) : IsW21 f :=
  ⟨f.smooth 2, fun _ _ ↦ integrable_iteratedDeriv_Schwarz⟩



/-- If `g` is a smooth, compactly supported truncation which equals `1` near the origin and
takes values in `[0, 1]`, then `v ↦ g (R⁻¹ * v) * ψ v` converges to `ψ` in the `W^{2,1}` norm
as `R → ∞`. -/
theorem W21_approximation {ψ : ℝ → ℂ} (hψ : IsW21 ψ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : HasCompactSupport g) (hg0 : g =ᶠ[𝓝 0] 1) (hgnn : ∀ v, 0 ≤ g v) (hg1 : ∀ v, g v ≤ 1) :
    Tendsto (fun R ↦ W21.norm (ψ - fun v ↦ (g (R⁻¹ * v) : ℂ) * ψ v)) atTop (𝓝 0) := by
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hψ'C : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψ.smooth).2.2
  have hψ'd : Differentiable ℝ (deriv ψ) := hψ'C.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hg'C : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hg'd : Differentiable ℝ (deriv g) := hg'C.differentiable (by simp)
  have hg'c : Continuous (deriv g) := hg'C.continuous
  have hg''c : Continuous (deriv (deriv g)) := hg'C.continuous_deriv le_rfl
  have hg's : HasCompactSupport (deriv g) := hgs.deriv
  have hg''s : HasCompactSupport (deriv (deriv g)) := hg's.deriv
  set h : ℝ → ℝ → ℝ := fun R v ↦ 1 - g (R⁻¹ * v) with hh
  set h' : ℝ → ℝ → ℝ := fun R v ↦ -(deriv g (R⁻¹ * v) * R⁻¹) with hh'
  set h'' : ℝ → ℝ → ℝ := fun R v ↦ -(deriv (deriv g) (R⁻¹ * v) * R⁻¹ * R⁻¹) with hh''
  have dscale (u : ℝ → ℝ) (hu : Differentiable ℝ u) (R v : ℝ) :
      HasDerivAt (fun v ↦ u (R⁻¹ * v)) (deriv u (R⁻¹ * v) * R⁻¹) v := by
    have h1 : HasDerivAt (fun v : ℝ ↦ R⁻¹ * v) R⁻¹ v := by
      simpa using (hasDerivAt_id v).const_mul R⁻¹
    simpa [Function.comp_def] using (hu (R⁻¹ * v)).hasDerivAt.comp v h1
  have dh (R v : ℝ) : HasDerivAt (h R) (h' R v) v := by
    simpa [hh, hh', sub_eq_add_neg] using (dscale g hgd R v).const_sub 1
  have dh' (R v : ℝ) : HasDerivAt (h' R) (h'' R v) v := by
    simpa [hh', hh'', Pi.neg_def] using ((dscale (deriv g) hg'd R v).mul_const R⁻¹).neg
  have ch {R} : Continuous (fun v ↦ (h R v : ℂ)) := by fun_prop
  have ch' {R} : Continuous (fun v ↦ (h' R v : ℂ)) := by fun_prop
  have ch'' {R} : Continuous (fun v ↦ (h'' R v : ℂ)) := by fun_prop
  have hh1 (R v : ℝ) : |h R v| ≤ 1 := by
    grind [abs_le, hg1 (R⁻¹ * v), hgnn (R⁻¹ * v)]
  have vR (v : ℝ) : Tendsto (fun R : ℝ ↦ R⁻¹ * v) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const v
  have eh (v : ℝ) : ∀ᶠ R in atTop, h R v = 0 := by
    filter_upwards [(vR v).eventually hg0] with R hR
    simp [*]
  have evg' : deriv g =ᶠ[𝓝 0] 0 := by
    filter_upwards [hg0.deriv] with x hx using by simpa using hx
  have evg'' : deriv (deriv g) =ᶠ[𝓝 0] 0 := by
    filter_upwards [evg'.deriv] with x hx using by simpa using hx
  have eh' (v : ℝ) : ∀ᶠ R in atTop, h' R v = 0 := by
    filter_upwards [(vR v).eventually evg'] with R hR
    simp [hh', show deriv g (R⁻¹ * v) = 0 from hR]
  have eh'' (v : ℝ) : ∀ᶠ R in atTop, h'' R v = 0 := by
    filter_upwards [(vR v).eventually evg''] with R hR
    simp [hh'', show deriv (deriv g) (R⁻¹ * v) = 0 from hR]
  convert_to Tendsto (fun R ↦ W21.norm (fun v ↦ (h R v : ℂ) * ψ v)) atTop (𝓝 0)
  · ext R; congr; ext v; simp [hh, sub_mul]
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
  · let F R v := ‖(h R v : ℂ) * ψ v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume :=
      .of_forall fun R ↦ (ch.mul hψ.smooth.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖ψ a‖ := by
      refine .of_forall fun R ↦ .of_forall fun v ↦ ?_
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      refine .of_forall fun v ↦ tendsto_nhds_of_eventually_eq ?_
      filter_upwards [eh v] with R hR; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 hψ.integrable.norm e4
  · let F R v := ‖(h'' R v : ℂ) * ψ v + 2 * (h' R v : ℂ) * deriv ψ v +
      (h R v : ℂ) * deriv (deriv ψ) v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have key R v : deriv (deriv (fun v ↦ (h R v : ℂ) * ψ v)) v =
          (h'' R v : ℂ) * ψ v + 2 * (h' R v : ℂ) * deriv ψ v +
            (h R v : ℂ) * deriv (deriv ψ) v := by
        have l3 v : HasDerivAt (fun v ↦ (h R v : ℂ) * ψ v)
            ((h' R v : ℂ) * ψ v + (h R v : ℂ) * deriv ψ v) v :=
          (dh R v).ofReal_comp.mul (hψd v).hasDerivAt
        have l5 : HasDerivAt (fun v ↦ (h' R v : ℂ) * ψ v)
            ((h'' R v : ℂ) * ψ v + (h' R v : ℂ) * deriv ψ v) v :=
          (dh' R v).ofReal_comp.mul (hψd v).hasDerivAt
        have l7 : HasDerivAt (fun v ↦ (h R v : ℂ) * deriv ψ v)
            ((h' R v : ℂ) * deriv ψ v + (h R v : ℂ) * deriv (deriv ψ) v) v :=
          (dh R v).ofReal_comp.mul (hψ'd v).hasDerivAt
        rw [funext fun v ↦ (l3 v).deriv]
        convert! (l5.add l7).deriv using 1; ring
      simp_rw [key, F]
    obtain ⟨c1, mg'⟩ : ∃ C, ∀ v, ‖deriv g v‖ ≤ C := by
      obtain ⟨x, hx⟩ := (continuous_norm.comp hg'c).exists_forall_ge_of_hasCompactSupport hg's.norm
      exact ⟨_, hx⟩
    obtain ⟨c2, mg''⟩ : ∃ C, ∀ v, ‖deriv (deriv g) v‖ ≤ C := by
      obtain ⟨x, hx⟩ :=
        (continuous_norm.comp hg''c).exists_forall_ge_of_hasCompactSupport hg''s.norm
      exact ⟨_, hx⟩
    have hc1n : (0 : ℝ) ≤ c1 := (norm_nonneg _).trans (mg' 0)
    have hc2n : (0 : ℝ) ≤ c2 := (norm_nonneg _).trans (mg'' 0)
    let bound v := c2 * ‖ψ v‖ + 2 * c1 * ‖deriv ψ v‖ + ‖deriv (deriv ψ) v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      refine .of_forall fun R ↦ (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul hψ.smooth.continuous).add ((continuous_const.mul ch').mul
        hψ'C.continuous)).add (ch.mul (hψ'C.continuous_deriv le_rfl))
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      filter_upwards [eventually_ge_atTop 1] with R hR
      have hR0 : (0 : ℝ) ≤ R := by linarith
      have hRi : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
      have hc1 v : |h' R v| ≤ c1 := by
        rw [hh']
        simp only [abs_neg, abs_mul, abs_inv, abs_of_nonneg hR0]
        calc |deriv g (R⁻¹ * v)| * R⁻¹ ≤ c1 * 1 := by
              gcongr
              · simpa using mg' _
          _ = c1 := mul_one _
      have hc2 v : |h'' R v| ≤ c2 := by
        rw [hh'']
        simp only [abs_neg, abs_mul, abs_inv, abs_of_nonneg hR0]
        calc |deriv (deriv g) (R⁻¹ * v)| * R⁻¹ * R⁻¹ ≤ c2 * 1 * 1 := by
              gcongr
              · simpa using mg'' _
          _ = c2 := by ring
      refine .of_forall fun v ↦ ?_
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · simpa using mul_le_mul (by simpa using hc2 v) le_rfl (by simp) hc2n
      · simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact hc1 v
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((hψ.integrable.norm).const_mul _).add ((hψ.integrable_deriv.norm).const_mul _)).add
      hψ.integrable_deriv_deriv.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      refine .of_forall fun v ↦ tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · exact tendsto_nhds_of_eventually_eq (by filter_upwards [eh'' v] with R hR; simp [hR])
      · exact tendsto_nhds_of_eventually_eq (by filter_upwards [eh' v] with R hR; simp [hR])
      · exact tendsto_nhds_of_eventually_eq (by filter_upwards [eh v] with R hR; simp [hR])
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
