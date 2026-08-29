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
-/

public section

open ArithmeticFunction.vonMangoldt Filter LSeries Chebyshev Real Finset
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
          _ ≤ (Real.log 4 + 4) * N := by
              rcases eq_or_ne N 0 with rfl | h
              · simp
              grw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊),
                ← psi_eq_sum_Icc, psi_le_const_mul_self <|
                sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
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
  refine Tendsto.congr (fun N ↦ ?_)
    (tendsto_residueClass_sum_div ((ZMod.isUnit_iff_coprime a q).mpr ha))
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  simp only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq,
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']

/-- **The weak prime number theorem** `∑ n < N, Λ n = N + o(N)`, as the `q = 1` case of the
weak prime number theorem in arithmetic progressions. -/
theorem WeakPNT : Tendsto (fun N ↦ (∑ i ∈ range N, Λ i) / N) atTop (𝓝 1) := by
  simpa [Nat.mod_one, Nat.totient_one] using WeakPNT_AP (q := 1) (a := 0) (by simp) one_pos
