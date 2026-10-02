import Jung5.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace Jung5

/-- A scaled order-four Hadamard configuration, embedded in the original R^5. -/
noncomputable def sharpPoint (i : Fin 4) : Point := fun k =>
  if k = 0 then
    if i = 0 ∨ i = 1 then (1 : ℝ) / 4 else -(1 / 4)
  else if k = 1 then
    if i = 0 ∨ i = 2 then (1 : ℝ) / 4 else -(1 / 4)
  else if k = 2 then
    if i = 0 ∨ i = 3 then (1 : ℝ) / 4 else -(1 / 4)
  else 0

theorem sharpPoint_pair (i j : Fin 4) (h : i ≠ j) :
    l1Dist (sharpPoint i) (sharpPoint j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [sharpPoint, l1Dist, Fin.sum_univ_five] at *

theorem sharpPoint_diameter_bound (i j : Fin 4) :
    l1Dist (sharpPoint i) (sharpPoint j) ≤ 1 := by
  by_cases h : i = j
  · subst j
    simp
  · rw [sharpPoint_pair i j h]

theorem sharpPoint_zero_radius (i : Fin 4) :
    l1Dist (sharpPoint i) (0 : Point) = (3 : ℝ) / 4 := by
  fin_cases i <;> norm_num [sharpPoint, l1Dist, Fin.sum_univ_five]

theorem opposite_quarters (t : ℝ) :
    (1 : ℝ) / 2 ≤ |1 / 4 - t| + |-(1 / 4) - t| := by
  have h := abs_sub_le ((1 : ℝ) / 4) t (-((1 : ℝ) / 4))
  rw [abs_sub_comm t (-((1 : ℝ) / 4))] at h
  norm_num at h
  exact h

theorem sharpPoint_sum_lower (c : Point) :
    (3 : ℝ) ≤ ∑ i : Fin 4, l1Dist (sharpPoint i) c := by
  have h₀ := opposite_quarters (c 0)
  have h₁ := opposite_quarters (c 1)
  have h₂ := opposite_quarters (c 2)
  have h₃ := abs_nonneg (c 3)
  have h₄ := abs_nonneg (c 4)
  rw [Fin.sum_univ_four]
  simp only [l1Dist, Fin.sum_univ_five]
  change (3 : ℝ) ≤
    (|1 / 4 - c 0| + |1 / 4 - c 1| + |1 / 4 - c 2| + |0 - c 3| + |0 - c 4|) +
    (|1 / 4 - c 0| + |-(1 / 4) - c 1| + |-(1 / 4) - c 2| + |0 - c 3| + |0 - c 4|) +
    (|-(1 / 4) - c 0| + |1 / 4 - c 1| + |-(1 / 4) - c 2| + |0 - c 3| + |0 - c 4|) +
    (|-(1 / 4) - c 0| + |-(1 / 4) - c 1| + |1 / 4 - c 2| + |0 - c 3| + |0 - c 4|)
  simp only [zero_sub, abs_neg]
  linarith

/-- For each unrestricted ambient center, some one of the four points is far. -/
theorem sharpPoint_radius_lower (c : Point) :
    ∃ i : Fin 4, (3 : ℝ) / 4 ≤ l1Dist (sharpPoint i) c := by
  by_contra h
  push Not at h
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ : Finset (Fin 4))) Finset.univ_nonempty
    (fun i _ => h i)
  have hbound := sharpPoint_sum_lower c
  norm_num at hsum
  linarith

/-- A concrete witness to sharpness, with the center quantified over all R^5. -/
theorem sharpness_witness :
    (∀ i j : Fin 4, i ≠ j → l1Dist (sharpPoint i) (sharpPoint j) = 1) ∧
    (∀ i : Fin 4, l1Dist (sharpPoint i) (0 : Point) = (3 : ℝ) / 4) ∧
    (∀ c : Point, ∃ i : Fin 4, (3 : ℝ) / 4 ≤ l1Dist (sharpPoint i) c) :=
  ⟨sharpPoint_pair, sharpPoint_zero_radius, sharpPoint_radius_lower⟩

end Jung5
