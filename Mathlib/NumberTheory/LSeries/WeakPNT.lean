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

open Nat hiding log
open ArithmeticFunction.vonMangoldt Filter LSeries Chebyshev Real Finset ZMod Asymptotics
open scoped Topology

/-- The Wiener–Ikehara theorem applied to the von Mangoldt function restricted to the residue
class `a` mod `q`: the average of `residueClass a` over `[0, x]` tends to `(q.totient)⁻¹`. -/
private theorem tendsto_residueClass_sum_div {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, residueClass a n) / x) atTop (𝓝 q.totient⁻¹) :=
  @WienerIkehara.tendsto_sum_div
    { f := residueClass a
      C := log 4 + 4
      bound N := calc
        _ ≤ ∑ i ∈ range N, Λ i := by
          refine sum_le_sum fun i _ ↦ ?_
          rw [norm_of_nonneg (residueClass_nonneg a i)]
          exact residueClass_le a i
        _ ≤ (log 4 + 4) * N := by
          rcases eq_or_ne N 0 with rfl | h
          · simp
          grw [range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊),
            ← psi_eq_sum_Icc, psi_le_const_mul_self <| sub_nonneg_of_le <|
            one_le_cast_iff_ne_zero.mpr h]
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
theorem ArithmeticFunction.vonMangoldt.tendsto_residueClass_sum_div_atTop {q a} [NeZero q]
    (ha : a.Coprime q) (ha' : a < q) : Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊,
      if n % q = a then Λ n else 0) / x) atTop (𝓝 q.totient⁻¹) := by
  refine (tendsto_residueClass_sum_div ((isUnit_iff_coprime a q).mpr ha)).congr (fun x ↦ ?_)
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  simp [residueClass, Set.indicator_apply, natCast_eq_natCast_iff', mod_eq_of_lt ha']
namespace Chebyshev

/-- **The prime number theorem, `ψ` form**: `ψ x / x → 1` as `x → ∞`. -/
theorem tendsto_psi_div_atTop : Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1) := by
  simpa [mod_one, totient_one, psi_eq_sum_Icc] using
    tendsto_residueClass_sum_div_atTop (q := 1) (a := 0) (by simp) one_pos

/-- **The prime number theorem, `ψ` form**: `ψ x ∼ x`. -/
theorem isEquivalent_psi_id : ψ ~[atTop] id := by
  rw [isEquivalent_iff_tendsto_one (by exact eventually_ne_atTop 0)]
  exact tendsto_psi_div_atTop.congr (by simp)

/-- **The prime number theorem, `θ` form**: `θ x / x → 1` as `x → ∞`. -/
theorem tendsto_theta_div_atTop : Tendsto (fun x ↦ θ x / x) atTop (𝓝 1) := by
  -- `(ψ - θ) / x → 0`, since `ψ x - θ x = O(√x) = o(x)`.
  suffices Tendsto (fun x ↦ (ψ x - θ x) / x) atTop (𝓝 0) by
    convert (tendsto_psi_div_atTop.sub this).congr' ?_
    · simp
    filter_upwards [eventually_gt_atTop 0]
    grind
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  have : Tendsto (fun x ↦ C * √x / x) atTop (𝓝 0) := by
    refine ((tendsto_const_nhds (x := C)).div_atTop tendsto_sqrt_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0]
    grind
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x _
    positivity [theta_le_psi x]
  · filter_upwards [eventually_gt_atTop 0] with x _
    grw [hC x]

/-- **The prime number theorem, `θ` form**: `θ x ~ x`. -/
theorem isEquivalent_theta_id : θ ~[atTop] id := by
  rw [isEquivalent_iff_tendsto_one (by exact eventually_ne_atTop 0)]
  exact tendsto_theta_div_atTop.congr (by simp)

/-- If the Chebyshev function `θ` is strictly larger at `b` than at `a`, then there is a prime in
the half-open interval `(a, b]`. -/
theorem exists_prime_of_theta_lt {a b} (hab : θ a < θ b) :
    ∃ p : ℕ, p.Prime ∧ ↑p ∈ Set.Ioc a b := by
  have : ⌊a⌋₊ ≤ ⌊b⌋₊ := by
    rw [theta_eq_theta_coe_floor a, theta_eq_theta_coe_floor b] at hab
    contrapose! hab
    exact theta_mono (mod_cast hab.le)
  have : ∑ p ∈ primesLE ⌊b⌋₊ \ primesLE ⌊a⌋₊, log (p : ℝ) + θ a = θ b := by
    simp_rw [theta_eq_sum_primesLE, Finset.sum_sdiff (primesLE_mono this)]
  have : ∑ p ∈ primesLE ⌊b⌋₊ \ primesLE ⌊a⌋₊, log p ≠ 0 := by linarith
  obtain ⟨p, hp⟩ := Finset.nonempty_of_sum_ne_zero this
  simp_rw [Finset.mem_sdiff, mem_primesLE] at hp
  obtain ⟨⟨hpb, hpp⟩, _⟩ := hp
  refine ⟨p, hpp, ?_, ?_⟩
  · grw [lt_floor_add_one a]
    exact_mod_cast (by grind)
  · rwa [← le_floor_iff]
    grw [← hpp.one_le] at hpb
    grind [one_le_floor_iff]

/-- **Small prime gaps.**  For every `ε > 0`, every sufficiently large `x` admits a prime in the
interval `(x, (1 + ε) * x]`. -/
theorem eventually_exists_prime_mem_Ioc {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∃ p : ℕ, p.Prime ∧ ↑p ∈ Set.Ioc x ((1 + ε) * x) := by
  have : Tendsto (fun x ↦ θ ((1 + ε) * x) / ((1 + ε) * x)) atTop (𝓝 1) :=
    tendsto_theta_div_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
  have : Tendsto (fun x ↦ θ ((1 + ε) * x) / x) atTop (𝓝 (1 + ε)) := by
    convert (this.mul_const (1 + ε)).congr' ?_
    · simp
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  have : Tendsto (fun x ↦ (θ ((1 + ε) * x) - θ x) / x) atTop (𝓝 ε) := by
    have := this.sub tendsto_theta_div_atTop
    rw [add_sub_cancel_left] at this
    exact this.congr' (by filter_upwards; grind)
  filter_upwards [(tendsto_order.1 this).1 0 hε, eventually_gt_atTop (0 : ℝ)] with x _ hx
  exact exists_prime_of_theta_lt (by grind [lt_div_iff₀ hx])

/-- **Primorial asymptotics**: `log (primorial n) / n → 1`. -/
theorem tendsto_log_primorial_div_atTop : Tendsto (fun n ↦ log (primorial n) / n) atTop (𝓝 1) :=
  (tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop).congr
  (by simp [theta_eq_log_primorial])

/-- **Primorial asymptotics**: `log (primorial n) ~ n`. -/
theorem isEquivalent_log_primorial_id : (fun n ↦ log (primorial n)) ~[atTop] (↑·) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with _ _ using by positivity)]
  exact tendsto_log_primorial_div_atTop.congr (by simp)

/-- **Least common multiple asymptotics**: `log (lcmUpto n) / n → 1`. -/
theorem tendsto_log_lcmUpto_div_atTop : Tendsto (fun n ↦ log (lcmUpto n) / n) atTop (𝓝 1) :=
  (tendsto_psi_div_atTop.comp tendsto_natCast_atTop_atTop).congr (by simp [psi_eq_log_lcmUpto])

/-- **Least common multiple asymptotics**: `log (lcmUpto n) ~ n`. -/
theorem isEquivalent_log_lcmUpto_id : (fun n ↦ log (lcmUpto n)) ~[atTop] (↑·) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with _ _ using by positivity)]
  exact tendsto_log_lcmUpto_div_atTop.congr (by simp)

end Chebyshev
