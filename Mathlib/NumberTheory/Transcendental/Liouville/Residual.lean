/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Instances.Irrational

/-!
# Density of Liouville numbers

In this file we prove that the set of Liouville numbers form a dense `Gδ` set. We also prove a
similar statement about irrational numbers.
-/


open scoped Filter

open Filter Set Metric

theorem setOf_liouville_eq_iInter_iUnion :
    { x | Liouville x } =
      ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b),
      ball ((a : ℝ) / b) (1 / (b : ℝ) ^ n) \ {(a : ℝ) / b} := by
  ext x
  simp only [mem_iInter, mem_iUnion, Liouville, mem_setOf_eq, exists_prop, mem_diff,
    mem_singleton_iff, mem_ball, Real.dist_eq, and_comm]

theorem IsGδ.setOf_liouville : IsGδ { x | Liouville x } := by
  rw [setOf_liouville_eq_iInter_iUnion]
  refine .iInter fun n => IsOpen.isGδ ?_
  refine isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => ?_
  exact isOpen_ball.inter isClosed_singleton.isOpen_compl


theorem setOf_liouville_eq_irrational_inter_iInter_iUnion :
    { x | Liouville x } =
      { x | Irrational x } ∩ ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b),
      ball (a / b) (1 / (b : ℝ) ^ n) := by
  refine Subset.antisymm ?_ ?_
  · refine subset_inter (fun x hx => hx.irrational) ?_
    rw [setOf_liouville_eq_iInter_iUnion]
    exact iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun _hb => diff_subset
  · simp only [inter_iInter, inter_iUnion, setOf_liouville_eq_iInter_iUnion]
    refine iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun hb => ?_
    rw [inter_comm]
    exact diff_subset_diff Subset.rfl (singleton_subset_iff.2 ⟨a / b, by norm_cast⟩)

/-- The set of Liouville numbers is a residual set. -/
theorem eventually_residual_liouville : ∀ᶠ x in residual ℝ, Liouville x := by
  rw [Filter.Eventually, setOf_liouville_eq_irrational_inter_iInter_iUnion]
  refine eventually_residual_irrational.and ?_
  refine residual_of_dense_Gδ ?_ (Rat.isDenseEmbedding_coe_real.dense.mono ?_)
  · exact .iInter fun n => IsOpen.isGδ <|
          isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => isOpen_ball
  · rintro _ ⟨r, rfl⟩
    simp only [mem_iInter, mem_iUnion]
    refine fun n => ⟨r.num * 2, r.den * 2, ?_, ?_⟩
    · have := r.pos; omega
    · convert @mem_ball_self ℝ _ (r : ℝ) _ _
      · push_cast
        -- Workaround for https://github.com/leanprover/lean4/pull/6438; this eliminates an
        -- `Expr.mdata` that would cause `norm_cast` to skip a numeral.
        rw [Eq.refl (2 : ℝ)]
        norm_cast
        simp [Rat.divInt_mul_right (two_ne_zero)]
      · refine one_div_pos.2 (pow_pos (Int.cast_pos.2 ?_) _)
        exact mul_pos (Int.natCast_pos.2 r.pos) zero_lt_two

/-- The set of Liouville numbers in dense. -/
theorem dense_liouville : Dense { x | Liouville x } :=
  dense_of_mem_residual eventually_residual_liouville
