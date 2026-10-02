import Jung5.ContactGeometry
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators
open Finset Set

namespace Jung5

/-- Finite sums are unchanged when an injective family is extended by zero. -/
theorem contact_sum_embedding {ι : Type*} [Fintype ι]
    (e : ι ↪ Fin 6) (a : ι → ℝ) (b : Fin 6 → ℝ)
    (hon : ∀ i, b (e i) = a i)
    (hoff : ∀ j, (¬ ∃ i, e i = j) → b j = 0) :
    ∑ j, b j = ∑ i, a i := by
  classical
  let u : Finset (Fin 6) := Finset.univ.image e
  calc
    ∑ j, b j = ∑ j ∈ u, b j := by
      apply (Finset.sum_subset (Finset.subset_univ u) ?_).symm
      intro j hj hju
      apply hoff
      rintro ⟨i, rfl⟩
      exact hju (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    _ = ∑ i, b (e i) := by
      exact Finset.sum_image (fun i hi j hj hij => e.injective hij)
    _ = ∑ i, a i := Finset.sum_congr rfl (fun i hi => hon i)

/-- Caratheodory gives at most six actual active rows. Any unused positions
are filled by an actual active row with zero coefficient, preserving activity
and original point membership at every one of the six positions. -/
theorem contact_six_active_family (X : Finset Point) (hne : X.Nonempty)
    (c : Point)
    (hmin : ∀ m : Point, contactRadius X hne c ≤ contactRadius X hne m) :
    ∃ (p s : Fin 6 → Point) (w : Fin 6 → ℝ),
      (∀ i, p i ∈ X) ∧ (∀ i, IsSign (s i)) ∧
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∀ k, ∑ i, w i * s i k = 0) ∧
      (∀ i, signDot (s i) (p i - c) = contactRadius X hne c) := by
  classical
  have hz := contact_active_convex_balance X hne c hmin
  obtain ⟨ι, hι, z, w, hsub, hind, hpos, hsum, hzero⟩ :=
    eq_pos_convex_span_of_mem_convexHull hz
  letI : Fintype ι := hι
  have hcard : Fintype.card ι ≤ 6 := by
    have hc := hind.card_le_finrank_succ
    have hd := (vectorSpan ℝ (Set.range z)).finrank_le
    have hdim : Module.finrank ℝ Point = 5 := Module.finrank_fin_fun ℝ
    exact hc.trans (Nat.add_le_add_right (hd.trans_eq hdim) 1)
  have hnonempty : Nonempty ι := by
    by_contra hn
    haveI : IsEmpty ι := not_nonempty_iff.mp hn
    simpa using hsum
  let i₀ : ι := Classical.choice hnonempty
  have hspec (i : ι) : IsSign (z i) ∧
      ∃ x ∈ X, signDot (z i) (x - c) = contactRadius X hne c :=
    contactActiveVector_spec X hne c (z i) (hsub ⟨i, rfl⟩)
  choose p hp hactive using (fun i => (hspec i).2)
  let e : ι ↪ Fin 6 :=
    { toFun := fun i => ⟨(Fintype.equivFin ι i).val,
        lt_of_lt_of_le (Fintype.equivFin ι i).isLt hcard⟩
      inj' := by
        intro i j hij
        apply (Fintype.equivFin ι).injective
        apply Fin.ext
        exact congrArg (fun z : Fin 6 => z.val) hij }
  let a : Fin 6 → ι := fun j =>
    if h : ∃ i, e i = j then h.choose else i₀
  let w₆ : Fin 6 → ℝ := fun j =>
    if h : ∃ i, e i = j then w h.choose else 0
  let p₆ : Fin 6 → Point := fun j => p (a j)
  let s₆ : Fin 6 → Point := fun j => z (a j)
  have ha (i : ι) : a (e i) = i := by
    have hi : ∃ j, e j = e i := ⟨i, rfl⟩
    dsimp [a]
    rw [dif_pos hi]
    exact e.injective hi.choose_spec
  have hw_on (i : ι) : w₆ (e i) = w i := by
    have hi : ∃ j, e j = e i := ⟨i, rfl⟩
    dsimp [w₆]
    rw [dif_pos hi, e.injective hi.choose_spec]
  have hw_off (j : Fin 6) (hj : ¬ ∃ i, e i = j) : w₆ j = 0 := by
    simp [w₆, hj]
  refine ⟨p₆, s₆, w₆, (fun j => hp (a j)), (fun j => (hspec (a j)).1),
    ?_, ?_, ?_, (fun j => hactive (a j))⟩
  · intro j
    dsimp [w₆]
    split_ifs with hj
    · exact (hpos hj.choose).le
    · exact le_rfl
  · exact (contact_sum_embedding e w w₆ hw_on hw_off).trans hsum
  · intro k
    have hbal : (∑ i, w i * z i k) = 0 := by
      have hk := congrArg (fun v : Point => v k) hzero
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hk
    calc
      (∑ j, w₆ j * s₆ j k) = ∑ i, w i * z i k := by
        apply contact_sum_embedding e
        · intro i
          simp only [hw_on, s₆, ha]
        · intro j hj
          rw [hw_off j hj, zero_mul]
      _ = 0 := hbal

end Jung5
