import Jung5.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
The coordinate bridge for the sharp ambient Jung bound in real `l1^5`.
The sorted lists retain all six labels, including repeated values. Consequently
zero gaps and tied medians require no generic-position assumption.
-/

open scoped BigOperators

namespace Jung5
namespace Gap
noncomputable section

/-- Five successive gaps of a six-tuple. -/
def stepGap (a : Fin 6 → ℝ) (r : Fin 5) : ℝ :=
  a r.succ - a r.castSucc

/-- The number of labels on the smaller side of a rank cut. -/
def gapCost (r : Fin 5) : ℕ := min (r.val + 1) (5 - r.val)

def rankSeparates (r : Fin 5) (i j : Fin 6) : Prop :=
  (i.val ≤ r.val ∧ ¬ j.val ≤ r.val) ∨
    (j.val ≤ r.val ∧ ¬ i.val ≤ r.val)

instance (r : Fin 5) (i j : Fin 6) : Decidable (rankSeparates r i j) := by
  unfold rankSeparates
  infer_instance

theorem stepGap_nonneg (a : Fin 6 → ℝ) (ha : Monotone a) (r : Fin 5) :
    0 ≤ stepGap a r := by
  apply sub_nonneg.mpr
  apply ha
  change r.val ≤ r.val + 1
  omega

/-- Exact scalar cut decomposition, with no strict-order requirement. -/
theorem ordered_pair (a : Fin 6 → ℝ) (ha : Monotone a) (i j : Fin 6) :
    (∑ r : Fin 5, if rankSeparates r i j then stepGap a r else 0) =
      |a i - a j| := by
  classical
  have habs : |a i - a j| = if i ≤ j then a j - a i else a i - a j := by
    by_cases hij : i ≤ j
    · rw [if_pos hij, abs_of_nonpos (sub_nonpos.mpr (ha hij)), neg_sub]
    · have hji : j ≤ i := (lt_of_not_ge hij).le
      rw [if_neg hij, abs_of_nonneg (sub_nonneg.mpr (ha hji))]
  rw [habs]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, rankSeparates, stepGap] <;> ring

/-- The third ordered value is a median even when values are repeated. -/
theorem ordered_median (a : Fin 6 → ℝ) (ha : Monotone a) :
    (∑ i : Fin 6, |a i - a 2|) =
      ∑ r : Fin 5, stepGap a r * (gapCost r : ℝ) := by
  have h02 : a 0 ≤ a 2 := ha (by decide)
  have h12 : a 1 ≤ a 2 := ha (by decide)
  have h23 : a 2 ≤ a 3 := ha (by decide)
  have h24 : a 2 ≤ a 4 := ha (by decide)
  have h25 : a 2 ≤ a 5 := ha (by decide)
  norm_num [Fin.sum_univ_succ, stepGap, gapCost,
    abs_of_nonpos (sub_nonpos.mpr h02),
    abs_of_nonpos (sub_nonpos.mpr h12),
    abs_of_nonneg (sub_nonneg.mpr h23),
    abs_of_nonneg (sub_nonneg.mpr h24),
    abs_of_nonneg (sub_nonneg.mpr h25)]
  ring

/-- The rank prefix as a set of original labels, transported by a permutation. -/
def rawPrefix (e : Equiv.Perm (Fin 6)) (r : Fin 5) : Finset (Fin 6) :=
  (Finset.univ.filter (fun i : Fin 6 => i.val ≤ r.val)).map e.toEmbedding

theorem mem_rawPrefix (e : Equiv.Perm (Fin 6)) (r : Fin 5) (i : Fin 6) :
    i ∈ rawPrefix e r ↔ (e.symm i).val ≤ r.val := by
  classical
  simp [rawPrefix, Equiv.eq_symm_apply]

theorem card_rawPrefix (e : Equiv.Perm (Fin 6)) (r : Fin 5) :
    (rawPrefix e r).card = r.val + 1 := by
  classical
  rw [rawPrefix, Finset.card_map]
  fin_cases r <;> decide

end
end Gap
end Jung5
