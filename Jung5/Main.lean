import Jung5.Contact
import Jung5.GapBridge
import Jung5.Extension
import Jung5.Sharpness

open scoped BigOperators

namespace Jung5

/-- The contact alternative is impossible by the six-point median theorem. -/
theorem unit_finite_enclosing : UnitFiniteEnclosing := by
  intro X hne hdiam
  rcases finite_contact_reduction X hne hdiam with hgood | hbad
  · exact hgood
  · rcases hbad with ⟨p, hp, hfar⟩
    obtain ⟨m, hm⟩ := six_point_median_bound p
      (fun i j => hdiam (p i) (hp i) (p j) (hp j))
    exact False.elim (not_lt_of_ge hm (hfar m))

/-- Every nonempty set of original real Manhattan diameter at most `D` admits
an unrestricted ambient center of Manhattan radius at most `3 * D / 4`.
No finite-support, coordinate-order or contact hypothesis is assumed. -/
theorem jung_l1_five (X : Set Point) (hne : X.Nonempty) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, l1Dist x y ≤ D) :
    ∃ c : Point, ∀ x ∈ X, l1Dist x c ≤ 3 * D / 4 :=
  enclosing_all_sets_of_unit_finite unit_finite_enclosing X hne D hD hdiam

/-- The complete upper bound with the original distance and dimension written
directly in its type, for straightforward statement auditing. -/
theorem jung_l1_five_explicit (X : Set (Fin 5 → ℝ)) (hne : X.Nonempty)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, (∑ k : Fin 5, |x k - y k|) ≤ D) :
    ∃ c : Fin 5 → ℝ, ∀ x ∈ X, (∑ k : Fin 5, |x k - c k|) ≤ 3 * D / 4 :=
  jung_l1_five X hne D hD hdiam

/-- The coefficient `3 / 4` in `jung_l1_five` is attained by a four-point
configuration, for centers quantified over all original ambient points. -/
theorem jung_l1_five_sharp :
    (∀ i j : Fin 4, i ≠ j → l1Dist (sharpPoint i) (sharpPoint j) = 1) ∧
    (∀ i : Fin 4, l1Dist (sharpPoint i) (0 : Point) = (3 : ℝ) / 4) ∧
    (∀ c : Point, ∃ i : Fin 4, (3 : ℝ) / 4 ≤ l1Dist (sharpPoint i) c) :=
  sharpness_witness

end Jung5
