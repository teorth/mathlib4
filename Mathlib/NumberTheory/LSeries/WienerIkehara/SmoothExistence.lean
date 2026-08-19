/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Alex Kontorovich, Terence Tao, Ruben Van de Velde,
  Arend Mellendijk, Alastair Irving, and the PrimeNumberTheoremAnd contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Tactic.Bound

/-!
# Smooth Urysohn lemma

A smooth function squeezed between the indicators of two nested intervals, used to approximate
indicator functions in the Wiener-Ikehara Tauberian theorem.

This file is a draft port from the `PrimeNumberTheoremAnd` project.
-/

@[expose] public section

namespace Function

theorem support_id {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ := by ext; simp

end Function

open MeasureTheory Set Real Function
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    indicator (Icc b c) 1 ≤ Ψ ∧ Ψ ≤ indicator (Ioo a d) 1 ∧
    (support Ψ = Ioo a d) := by
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, _⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (modelWithCornersSelf ℝ ℝ) (s := Iic a ∪ Ici d) (t := Icc b c)
    (isClosed_Iic.union isClosed_Ici) isClosed_Icc (by grind)
  simp only [range_subset_iff] at *
  refine ⟨Ψ, hΨSmooth.contDiff,
    HasCompactSupport.of_support_subset_isCompact (K := Icc a d) isCompact_Icc (by simp; grind),
    indicator_le' (by simp; grind) fun x _ ↦ (hΨrange x).1,
    fun x ↦ le_indicator_apply (fun _ ↦ (hΨrange x).2) (fun hx ↦ by grind),
    by ext; simp [← hΨ0]⟩

lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Icc (1 / 2) 2 ∧ 0 < ∫ x in Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := ∫ x in Ici 0, ν x / x
    refine ⟨(ν · / c), hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [support_div, support_const (ne_of_lt hνpos).symm, inter_univ]
      exact hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ :=
    smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  unfold indicator at hν0 hν1
  refine ⟨ν, hνContDiff, fun x ↦ le_trans (by simp [apply_ite]) (hν0 x), by grind, ?_ ⟩
  rw [integral_pos_iff_support_of_nonneg]
  · have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
      grind
    simp
    grind [support_id, volume_Ioo, ENNReal.ofReal_pos]
  · simp_rw [Pi.le_def, Pi.zero_apply]
    intro y
    by_cases h : y ∈ support ν
    · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
      grind
    · simp only [mem_support, ne_eq, not_not] at h
      simp [h]
  · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
      rw [support_div, hνSupport]
      exact (inter_subset_left).trans Ioo_subset_Icc_self
    apply (integrableOn_iff_integrable_of_support_subset this).mp
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply hνContDiff.continuous.continuousOn.div continuousOn_id (by grind)
