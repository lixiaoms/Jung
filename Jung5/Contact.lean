import Jung5.ContactExtraction

/-!
The finite original l1 minimum and its active sign forms are reduced to
six original points. The alternative obstruction is designed to be contradicted
by the coordinate median theorem, with repetitions and coordinate ties allowed.
-/

open scoped BigOperators

namespace Jung5

theorem finite_contact_reduction
    (X : Finset Point) (hne : X.Nonempty)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, l1Dist x y ≤ 1) :
    (∃ c : Point, ∀ x ∈ X, l1Dist x c ≤ (3 : ℝ) / 4) ∨
    ∃ p : Fin 6 → Point,
      (∀ i, p i ∈ X) ∧
      ∀ m : Point, (9 : ℝ) / 2 < ∑ i, l1Dist (p i) m := by
  obtain ⟨c, hmin⟩ := exists_contact_minimizer X hne
  by_cases hR : contactRadius X hne c ≤ (3 : ℝ) / 4
  · exact Or.inl ⟨c, fun x hx =>
      (contact_distance_le_radius X hne c x hx).trans hR⟩
  · obtain ⟨p, s, w, hp, hs, hw, hsum, hbal, hactive⟩ :=
      contact_six_active_family X hne c hmin
    refine Or.inr ⟨p, hp, ?_⟩
    exact six_contact_obstruction p s w c (contactRadius X hne c)
      hs hw hsum hbal hactive
      (fun i j => hdiam (p i) (hp i) (p j) (hp j)) (lt_of_not_ge hR)

end Jung5
