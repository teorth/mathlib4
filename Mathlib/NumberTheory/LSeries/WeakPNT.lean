/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Francisco Antonio Balderas, Vincent Beffara, Alex Kontorovich, Terence Tao,
  Ruben Van de Velde, Arend Mellendijk, Alastair Irving
-/
module

public import Mathlib.NumberTheory.LSeries.WienerIkehara

/-!
# The weak prime number theorem

We deduce the weak prime number theorem, and its version in arithmetic progressions, from the
Wiener–Ikehara Tauberian theorem `WienerIkehara.tendsto_sum_div`.

## Main results

* `WeakPNT_AP`: the weak prime number theorem in arithmetic progressions: for `a` coprime to `q`,
  `∑ n < N, n ≡ a [MOD q], Λ n = N / q.totient + o(N)`.
* `WeakPNT`: the weak prime number theorem `∑ n < N, Λ n = N + o(N)`, the `q = 1` case.
* `Chebyshev.isEquivalent_psi_id`: the `ψ`-form of the prime number theorem, `ψ x ~ x`
  (equivalently `Chebyshev.tendsto_psi_div_atTop`, `ψ x / x → 1`).
* `Chebyshev.isEquivalent_theta_id`: the `θ`-form, `θ x ~ x`.
* `Chebyshev.isEquivalent_log_primorial_id`: `log (primorial n) ~ n`.
-/

public section

open ArithmeticFunction.vonMangoldt Filter LSeries Chebyshev Real Finset ZMod
open scoped Topology

/-- The Wiener–Ikehara theorem applied to the von Mangoldt function restricted to the residue
class `a` mod `q`: the average of `residueClass a` over `[0, N)` tends to `(q.totient)⁻¹`. -/
private theorem tendsto_residueClass_sum_div {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun N ↦ (∑ i ∈ range N, residueClass a i) / N) atTop (𝓝 (q.totient : ℝ)⁻¹) :=
  @WienerIkehara.tendsto_sum_div
    { f := residueClass a
      C := log 4 + 4
      bound N := by
        calc ∑ i ∈ range N, ‖residueClass a i‖
            ≤ ∑ i ∈ range N, Λ i := by
              refine sum_le_sum fun i _ ↦ ?_
              rw [norm_of_nonneg (residueClass_nonneg a i)]
              exact residueClass_le a i
          _ ≤ (log 4 + 4) * N := by
              rcases eq_or_ne N 0 with rfl | h
              · simp
              grw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊),
                ← psi_eq_sum_Icc, psi_le_const_mul_self <| sub_nonneg_of_le <|
                Nat.one_le_cast_iff_ne_zero.mpr h]
              gcongr
              linarith
      A := (q.totient : ℝ)⁻¹
      hA := by positivity
      G := LFunctionResidueClassAux a
      hG := continuousOn_LFunctionResidueClassAux a
      hG' s hs := by rw [eqOn_LFunctionResidueClassAux ha hs]; push_cast; ring
      hf σ hσ := LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| by
          rw [Complex.ofReal_re]; exact_mod_cast hσ
      hpos := residueClass_nonneg a }

/-- **The weak prime number theorem in arithmetic progressions.**  For `a` coprime to `q`, the
von Mangoldt function summed over `n < N` with `n ≡ a mod q` grows like `N / q.totient`. -/
theorem WeakPNT_AP {q a : ℕ} [NeZero q] (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun N ↦ (∑ n ∈ range N, if n % q = a then Λ n else 0) / N) atTop
      (𝓝 (1 / (q.totient : ℝ))) := by
  rw [one_div]
  refine (tendsto_residueClass_sum_div ((isUnit_iff_coprime a q).mpr ha)).congr (fun N ↦ ?_)
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  simp only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt ha']

/-- **The weak prime number theorem** `∑ n < N, Λ n = N + o(N)`, as the `q = 1` case of the
weak prime number theorem in arithmetic progressions. -/
theorem WeakPNT : Tendsto (fun N ↦ (∑ i ∈ range N, Λ i) / N) atTop (𝓝 1) := by
  simpa [Nat.mod_one, Nat.totient_one] using WeakPNT_AP (q := 1) (a := 0) (by simp) one_pos

/-- **The prime number theorem, `ψ` form**: the Chebyshev function `ψ x = ∑ n ≤ x, Λ n` satisfies
`ψ x / x → 1` as `x → ∞`. -/
theorem Chebyshev.tendsto_psi_div_atTop : Tendsto (fun x : ℝ ↦ ψ x / x) atTop (𝓝 1) := by
  -- First, the version over the naturals: `ψ N / N → 1`.
  have hNat : Tendsto (fun N : ℕ ↦ ψ (N : ℝ) / N) atTop (𝓝 1) := by
    have e : ∀ N : ℕ, ψ (N : ℝ) = ∑ i ∈ range (N + 1), Λ i := fun N ↦ by
      rw [psi_eq_sum_Icc, Nat.floor_natCast, Nat.range_eq_Icc_zero_sub_one (N + 1) (by omega)]
      simp
    have h1 : Tendsto (fun N : ℕ ↦ (∑ i ∈ range (N + 1), Λ i) / ((N : ℝ) + 1)) atTop (𝓝 1) := by
      simpa [Function.comp_def, Nat.cast_add_one] using WeakPNT.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
      have hc : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      have h : Tendsto (fun N : ℕ ↦ 1 + (N : ℝ)⁻¹) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add hc
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      field_simp
    have hmul := h1.mul h2
    rw [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [e N]; field_simp
  -- Upgrade to the reals via the floor.
  have hm := (hNat.comp tendsto_nat_floor_atTop).mul tendsto_nat_floor_div_atTop
  rw [one_mul] at hm
  refine hm.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hx.le
  rw [Function.comp_apply, psi_eq_psi_coe_floor x]
  field_simp

open Asymptotics in
/-- **The prime number theorem, `ψ` form**: the Chebyshev function `ψ` is asymptotically
equivalent to the identity, i.e. `ψ x ~ x`. -/
theorem Chebyshev.isEquivalent_psi_id : ψ ~[atTop] (id : ℝ → ℝ) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx using hx.ne')]
  exact Chebyshev.tendsto_psi_div_atTop.congr fun x ↦ by simp [Pi.div_apply]

/-- **The prime number theorem, `θ` form**: the Chebyshev function `θ x = ∑ p ≤ x, log p`
satisfies `θ x / x → 1` as `x → ∞`.  This is `chebyshev_asymptotic` in the PNT project. -/
theorem Chebyshev.tendsto_theta_div_atTop : Tendsto (fun x : ℝ ↦ θ x / x) atTop (𝓝 1) := by
  -- `(ψ - θ) / x → 0`, since `ψ x - θ x ≤ 2 √x log x = o(x)`.
  have hlog : Tendsto (fun x : ℝ ↦ log x / √x) atTop (𝓝 0) := by
    refine ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero).congr
      fun x ↦ ?_
    rw [Real.sqrt_eq_rpow]
  have hub : Tendsto (fun x : ℝ ↦ 2 * √x * log x / x) atTop (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ ↦ 2 * (log x / √x)) atTop (𝓝 0) := by
      simpa using hlog.const_mul (2 : ℝ)
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hsx : (0 : ℝ) < √x := Real.sqrt_pos.mpr hx
    have h1 : √x * √x = x := Real.mul_self_sqrt hx.le
    rw [mul_assoc, mul_div_assoc]
    congr 1
    rw [div_eq_div_iff hsx.ne' hx.ne']
    linear_combination -log x * h1
  have hdiff : Tendsto (fun x : ℝ ↦ (ψ x - θ x) / x) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (sub_nonneg.mpr (theta_le_psi x)) hx.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have : (0 : ℝ) ≤ x := by linarith
      gcongr
      exact psi_sub_theta_le hx
  have hcomb := Chebyshev.tendsto_psi_div_atTop.sub hdiff
  simp only [sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [div_sub_div_same]; congr 1; ring

open Asymptotics in
/-- **The prime number theorem, `θ` form**: the Chebyshev function `θ` is asymptotically
equivalent to the identity, i.e. `θ x ~ x`. -/
theorem Chebyshev.isEquivalent_theta_id : θ ~[atTop] (id : ℝ → ℝ) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx using hx.ne')]
  exact Chebyshev.tendsto_theta_div_atTop.congr fun x ↦ by simp [Pi.div_apply]

/-- **Primorial asymptotics**: `log (primorial n) / n → 1`, since `θ n = log (primorial n)`. -/
theorem Chebyshev.tendsto_log_primorial_div_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (primorial n) / n) atTop (𝓝 1) := by
  refine (tendsto_theta_div_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).congr fun n ↦ ?_
  rw [Function.comp_apply, theta_eq_log_primorial, Nat.floor_natCast]

open Asymptotics in
/-- **Primorial asymptotics**: `log (primorial n) ~ n`, a consequence of the prime number theorem
via `θ n = log (primorial n)`. -/
theorem Chebyshev.isEquivalent_log_primorial_id :
    (fun n : ℕ ↦ Real.log (primorial n)) ~[atTop] (fun n ↦ (n : ℝ)) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with n hn using by positivity)]
  exact tendsto_log_primorial_div_atTop.congr fun n ↦ by simp [Pi.div_apply]
