import Jung5.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators
open Set

namespace Jung5

/-- A proof interface, discharged by the contact and cut arguments in Main. -/
def UnitFiniteEnclosing : Prop :=
  ∀ X : Finset Point, X.Nonempty →
    (∀ x ∈ X, ∀ y ∈ X, l1Dist x y ≤ 1) →
    ∃ c : Point, ∀ x ∈ X, l1Dist x c ≤ (3 : ℝ) / 4

theorem finite_enclosing_scaled (hunit : UnitFiniteEnclosing)
    (D : ℝ) (hD : 0 ≤ D) (X : Finset Point) (hne : X.Nonempty)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, l1Dist x y ≤ D) :
    ∃ c : Point, ∀ x ∈ X, l1Dist x c ≤ 3 * D / 4 := by
  classical
  rcases hne with ⟨x₀, hx₀⟩
  rcases eq_or_lt_of_le hD with hzero | hpos
  · subst D
    refine ⟨x₀, ?_⟩
    intro x hx
    simpa using hdiam x hx x₀ hx₀
  · let f : Point → Point := fun x k => D⁻¹ * x k
    let Y := X.image f
    have hY : Y.Nonempty := ⟨f x₀, Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩⟩
    have hnorm (x y : Point) : l1Dist (f x) (f y) = D⁻¹ * l1Dist x y := by
      simpa [f, abs_of_pos (inv_pos.mpr hpos)] using l1Dist_scale D⁻¹ x y
    have hYdiam : ∀ x ∈ Y, ∀ y ∈ Y, l1Dist x y ≤ 1 := by
      intro x hx y hy
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      rw [hnorm]
      calc
        D⁻¹ * l1Dist a b ≤ D⁻¹ * D :=
          mul_le_mul_of_nonneg_left (hdiam a ha b hb) (inv_nonneg.mpr hD)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    obtain ⟨c, hc⟩ := hunit Y hY hYdiam
    refine ⟨fun k => D * c k, ?_⟩
    intro x hx
    have hfx : f x ∈ Y := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hinverse : (fun k => D * f x k) = x := by
      funext k
      dsimp [f]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    have heq : l1Dist x (fun k => D * c k) = D * l1Dist (f x) c := by
      calc
        l1Dist x (fun k => D * c k) =
            l1Dist (fun k => D * f x k) (fun k => D * c k) := by rw [hinverse]
        _ = D * l1Dist (f x) c := by
          rw [l1Dist_scale, abs_of_pos hpos]
    rw [heq]
    calc
      D * l1Dist (f x) c ≤ D * ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (hc (f x) hfx) hD
      _ = 3 * D / 4 := by ring

theorem continuous_l1Dist_center (x : Point) :
    Continuous (fun c : Point => l1Dist x c) := by
  unfold l1Dist
  apply continuous_finset_sum
  intro k _
  exact (continuous_const.sub (continuous_apply k)).abs

theorem isClosed_l1_center_constraint (x : Point) (r : ℝ) :
    IsClosed {c : Point | l1Dist x c ≤ r} :=
  isClosed_le (continuous_l1Dist_center x) continuous_const

/-- Compactness uses the product topology only; the constraint is still l1. -/
theorem isCompact_l1_center_constraint (x : Point) (r : ℝ) (hr : 0 ≤ r) :
    IsCompact {c : Point | l1Dist x c ≤ r} := by
  apply (isCompact_closedBall x r).of_isClosed_subset
    (isClosed_l1_center_constraint x r)
  intro c hc
  apply (dist_pi_le_iff hr).mpr
  intro k
  simpa only [Real.dist_eq, abs_sub_comm] using
    (abs_coordinate_sub_le x c k).trans hc

/-- Finite intersection extension; the final Main theorem discharges hunit. -/
theorem enclosing_all_sets_of_unit_finite (hunit : UnitFiniteEnclosing)
    (X : Set Point) (hne : X.Nonempty) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, l1Dist x y ≤ D) :
    ∃ c : Point, ∀ x ∈ X, l1Dist x c ≤ 3 * D / 4 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  let r : ℝ := 3 * D / 4
  have hr : 0 ≤ r := by dsimp [r]; linarith
  let K : Set Point := {c | l1Dist x₀ c ≤ r}
  let C : X → Set Point := fun x => {c | l1Dist x.val c ≤ r}
  have hK : IsCompact K := isCompact_l1_center_constraint x₀ r hr
  have hC : ∀ x, IsClosed (C x) := fun x => isClosed_l1_center_constraint x.val r
  have hfinite : ∀ u : Finset X, (K ∩ ⋂ x ∈ u, C x).Nonempty := by
    intro u
    let F : Finset Point := insert x₀ (u.image Subtype.val)
    have hFne : F.Nonempty := ⟨x₀, Finset.mem_insert_self _ _⟩
    have hFX : ∀ x ∈ F, x ∈ X := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact h ▸ hx₀
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp h
        exact y.property
    obtain ⟨c, hc⟩ := finite_enclosing_scaled hunit D hD F hFne
      (fun x hx y hy => hdiam x (hFX x hx) y (hFX y hy))
    refine ⟨c, ?_, ?_⟩
    · exact hc x₀ (Finset.mem_insert_self _ _)
    · refine Set.mem_iInter.mpr (fun x => Set.mem_iInter.mpr (fun hx => ?_))
      exact hc x.val (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  obtain ⟨c, _, hc⟩ := hK.inter_iInter_nonempty C hC hfinite
  refine ⟨c, ?_⟩
  intro x hx
  exact Set.mem_iInter.mp hc ⟨x, hx⟩

end Jung5
