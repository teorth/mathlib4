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

* `ArithmeticFunction.vonMangoldt.tendsto_residueClass_sum_div_atTop`: the weak prime number
  theorem in arithmetic progressions: for `a` coprime to `q`,
  `∑ n ≤ x, n ≡ a [MOD q], Λ n = x / q.totient + o(x)`.
* `ArithmeticFunction.vonMangoldt.tendsto_sum_div_atTop`: the weak prime number theorem
  `∑ n ≤ x, Λ n = x + o(x)`, the `q = 1` case.
* `Chebyshev.isEquivalent_psi_id`: the `ψ`-form of the prime number theorem, `ψ x ~ x`
  (equivalently `Chebyshev.tendsto_psi_div_atTop`, `ψ x / x → 1`).
* `Chebyshev.isEquivalent_theta_id`: the `θ`-form, `θ x ~ x`.
* `Chebyshev.eventually_exists_prime_lt_and_le_mul`: for every `ε > 0`, every sufficiently large
  `x` has a prime in `(x, (1 + ε) * x]`.
* `Chebyshev.isEquivalent_log_primorial_id`: `log (primorial n) ~ n`.
* `Chebyshev.isEquivalent_log_lcmUpto_id`: `log (Nat.lcmUpto n) ~ n`.
-/

public section

open ArithmeticFunction.vonMangoldt Filter LSeries Chebyshev Real Finset ZMod Asymptotics
open scoped Topology

/-- The Wiener–Ikehara theorem applied to the von Mangoldt function restricted to the residue
class `a` mod `q`: the average of `residueClass a` over `[0, x]` tends to `(q.totient)⁻¹`. -/
private theorem tendsto_residueClass_sum_div {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, residueClass a n) / x) atTop (𝓝 q.totient⁻¹) :=
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
      A := q.totient⁻¹
      hA := by positivity
      G := LFunctionResidueClassAux a
      hG := continuousOn_LFunctionResidueClassAux a
      hG' s hs := by rw [eqOn_LFunctionResidueClassAux ha hs]; push_cast; ring
      hf σ hσ := LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| by
          rw [Complex.ofReal_re]; exact_mod_cast hσ
      hpos := residueClass_nonneg a }

/-- **The weak prime number theorem in arithmetic progressions.**  For `a` coprime to `q`, the
von Mangoldt function summed over `n ≤ x` with `n ≡ a mod q` grows like `x / q.totient`. -/
theorem ArithmeticFunction.vonMangoldt.tendsto_residueClass_sum_div_atTop {q a : ℕ} [NeZero q]
    (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, if n % q = a then Λ n else 0) / x) atTop
      (𝓝 (1 / q.totient)) := by
  rw [one_div]
  refine (tendsto_residueClass_sum_div ((isUnit_iff_coprime a q).mpr ha)).congr (fun x ↦ ?_)
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  simp only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt ha']

namespace Chebyshev

/-- **The prime number theorem, `ψ` form**: `ψ x / x → 1` as `x → ∞`. -/
theorem tendsto_psi_div_atTop :
    Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1) := by
  simpa [Nat.mod_one, Nat.totient_one, psi_eq_sum_Icc] using
    tendsto_residueClass_sum_div_atTop (q := 1) (a := 0) (by simp) one_pos

/-- **The prime number theorem, `ψ` form**: `ψ x ∼ x`. -/
theorem isEquivalent_psi_id : ψ ~[atTop] id := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx using hx.ne')]
  exact tendsto_psi_div_atTop.congr fun _ ↦ by simp [Pi.div_apply]

/-- **The prime number theorem, `θ` form**: `θ x / x → 1` as `x → ∞`. -/
theorem tendsto_theta_div_atTop : Tendsto (fun x ↦ θ x / x) atTop (𝓝 1) := by
  -- `(ψ - θ) / x → 0`, since `ψ x - θ x = O(√x) = o(x)`.
  suffices h : Tendsto (fun x ↦ (ψ x - θ x) / x) atTop (𝓝 0) by
    have := tendsto_psi_div_atTop.sub h
    convert this.congr' ?_
    · simp
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_sub_div_same]; congr 1; ring
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  have hub : Tendsto (fun x ↦ C * √x / x) atTop (𝓝 0) := by
    refine ((tendsto_const_nhds (x := C)).div_atTop tendsto_sqrt_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_eq_div_iff (sqrt_pos.mpr hx).ne' hx.ne', mul_assoc, mul_self_sqrt hx.le]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (sub_nonneg.mpr (theta_le_psi x)) hx.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    gcongr
    exact hC x

/-- **The prime number theorem, `θ` form**: `θ x ~ x`. -/
theorem isEquivalent_theta_id : θ ~[atTop] (id : ℝ → ℝ) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx using hx.ne')]
  exact tendsto_theta_div_atTop.congr fun x ↦ by simp [Pi.div_apply]

/-- If the Chebyshev function `θ` is strictly larger at `b` than at `a`, then there is a prime in
the half-open interval `(a, b]`. -/
theorem exists_prime_of_theta_lt {a b : ℝ} (hab : θ a < θ b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := by
    by_contra h
    rw [not_le] at h
    rw [theta_eq_theta_coe_floor a, theta_eq_theta_coe_floor b] at hab
    exact absurd (theta_mono (by exact_mod_cast h.le)) (not_le.mpr hab)
  have hsub : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ := Nat.primesLE_mono hfloor
  have key : ∑ p ∈ Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊, log (p : ℝ) = θ b - θ a := by
    rw [eq_sub_iff_add_eq, theta_eq_sum_primesLE a, Finset.sum_sdiff hsub,
      theta_eq_sum_primesLE b]
  have hpos : (0 : ℝ) < ∑ p ∈ Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊, log (p : ℝ) := by
    rw [key]; linarith
  obtain ⟨p, hp⟩ := Finset.nonempty_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
  obtain ⟨⟨hpb, hpp⟩, hpa⟩ := hp
  have hap : ⌊a⌋₊ < p := by
    by_contra hle
    exact hpa ⟨not_lt.mp hle, hpp⟩
  refine ⟨p, hpp, ?_, ?_⟩
  · calc a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
      _ ≤ (p : ℝ) := by exact_mod_cast hap
  · have hb_pos : 0 < ⌊b⌋₊ := lt_of_lt_of_le hpp.pos hpb
    calc (p : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast hpb
      _ ≤ b := Nat.floor_le (by linarith [Nat.floor_pos.mp hb_pos])

/-- **Prime gaps from the prime number theorem.**  For every `ε > 0`, every sufficiently large
`x` admits a prime in the interval `(x, (1 + ε) * x]`. -/
theorem eventually_exists_prime_lt_and_le_mul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ (1 + ε) * x := by
  have hlin : Tendsto (fun x : ℝ ↦ (1 + ε) * x) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith) tendsto_id
  have hcomp : Tendsto (fun x ↦ θ ((1 + ε) * x) / ((1 + ε) * x)) atTop (𝓝 1) :=
    tendsto_theta_div_atTop.comp hlin
  have h1e : (1 : ℝ) + ε ≠ 0 := ne_of_gt (by linarith)
  have h2 : Tendsto (fun x ↦ θ ((1 + ε) * x) / x) atTop (𝓝 (1 + ε)) := by
    have hmul := hcomp.mul_const (1 + ε)
    rw [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := hx.ne'
    field_simp
  have hdiff : Tendsto (fun x ↦ (θ ((1 + ε) * x) - θ x) / x) atTop (𝓝 ε) := by
    have hs := h2.sub tendsto_theta_div_atTop
    rw [add_sub_cancel_left] at hs
    refine hs.congr' ?_
    filter_upwards with x
    rw [sub_div]
  filter_upwards [(tendsto_order.1 hdiff).1 0 hε, eventually_gt_atTop (0 : ℝ)] with x hx0 hxpos
  have hlt : θ x < θ ((1 + ε) * x) := by
    rw [lt_div_iff₀ hxpos, zero_mul] at hx0
    linarith
  exact exists_prime_of_theta_lt hlt

/-- **Primorial asymptotics**: `log (primorial n) / n → 1`. -/
theorem tendsto_log_primorial_div_atTop :
    Tendsto (fun n ↦ log (primorial n) / n) atTop (𝓝 1) := by
  refine (tendsto_theta_div_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).congr fun n ↦ ?_
  rw [Function.comp_apply, theta_eq_log_primorial, Nat.floor_natCast]

/-- **Primorial asymptotics**: `log (primorial n) ~ n`. -/
theorem isEquivalent_log_primorial_id :
    (fun n ↦ log (primorial n)) ~[atTop] (fun n ↦ (n : ℝ)) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with n hn using by positivity)]
  exact tendsto_log_primorial_div_atTop.congr fun n ↦ by simp [Pi.div_apply]

/-- **Least common multiple asymptotics**: `log (Nat.lcmUpto n) / n → 1`. -/
theorem tendsto_log_lcmUpto_div_atTop :
    Tendsto (fun n ↦ log (Nat.lcmUpto n) / n) atTop (𝓝 1) := by
  refine (tendsto_psi_div_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).congr fun n ↦ ?_
  rw [Function.comp_apply, psi_eq_log_lcmUpto]

/-- **Least common multiple asymptotics**: `log (Nat.lcmUpto n) ~ n`. -/
theorem isEquivalent_log_lcmUpto_id :
    (fun n ↦ log (Nat.lcmUpto n)) ~[atTop] (fun n ↦ (n : ℝ)) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with n hn using by positivity)]
  exact tendsto_log_lcmUpto_div_atTop.congr fun n ↦ by simp [Pi.div_apply]

end Chebyshev
