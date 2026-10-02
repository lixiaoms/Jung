import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace Jung5

abbrev Point := Fin 5 → ℝ

/-- The original Manhattan distance, explicitly independent of the Pi norm. -/
def l1Dist (x y : Point) : ℝ := ∑ k, |x k - y k|

theorem l1Dist_nonneg (x y : Point) : 0 ≤ l1Dist x y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

@[simp] theorem l1Dist_self (x : Point) : l1Dist x x = 0 := by
  simp [l1Dist]

theorem l1Dist_symm (x y : Point) : l1Dist x y = l1Dist y x := by
  unfold l1Dist
  exact Finset.sum_congr rfl (fun _ _ => abs_sub_comm _ _)

theorem l1Dist_triangle (x y z : Point) :
    l1Dist x z ≤ l1Dist x y + l1Dist y z := by
  unfold l1Dist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_sub_le _ _ _)

theorem abs_coordinate_sub_le (x y : Point) (k : Fin 5) :
    |x k - y k| ≤ l1Dist x y := by
  exact Finset.single_le_sum (fun i _ => abs_nonneg (x i - y i)) (Finset.mem_univ k)

theorem l1Dist_scale (a : ℝ) (x y : Point) :
    l1Dist (fun k => a * x k) (fun k => a * y k) = |a| * l1Dist x y := by
  simp only [l1Dist, ← mul_sub, abs_mul, Finset.mul_sum]

end Jung5
