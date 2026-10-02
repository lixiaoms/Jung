import Jung5.ContactCounting
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

open scoped BigOperators
open Finset Set

namespace Jung5

/-- A finite parametrization of all original l1 norming forms. -/
abbrev ContactSigns := Fin 5 → Bool

def contactSignVector (s : ContactSigns) : Point :=
  fun k => if s k then 1 else -1

theorem contactSignVector_isSign (s : ContactSigns) :
    IsSign (contactSignVector s) := by
  intro k
  unfold contactSignVector
  split <;> simp

noncomputable def contactNormingSigns (x c : Point) : ContactSigns :=
  fun k => decide (0 ≤ x k - c k)

theorem contact_norming_identity (x c : Point) :
    signDot (contactSignVector (contactNormingSigns x c)) (x - c) =
      l1Dist x c := by
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : 0 ≤ x k - c k
  · simp [contactSignVector, contactNormingSigns, h, abs_of_nonneg h]
  · simp [contactSignVector, contactNormingSigns, h, abs_of_neg (lt_of_not_ge h)]

/-- This is the maximum of the original Manhattan distances over the full X. -/
noncomputable def contactRadius (X : Finset Point) (hne : X.Nonempty)
    (c : Point) : ℝ := X.sup' hne (fun x => l1Dist x c)

theorem contact_distance_le_radius (X : Finset Point) (hne : X.Nonempty)
    (c x : Point) (hx : x ∈ X) : l1Dist x c ≤ contactRadius X hne c := by
  exact Finset.le_sup' (fun x => l1Dist x c) hx

theorem contact_radius_nonneg (X : Finset Point) (hne : X.Nonempty)
    (c : Point) : 0 ≤ contactRadius X hne c := by
  have hne' := hne
  obtain ⟨x, hx⟩ := hne'
  exact (l1Dist_nonneg x c).trans (contact_distance_le_radius X hne c x hx)

theorem continuous_contact_distance (x : Point) :
    Continuous (fun c : Point => l1Dist x c) := by
  unfold l1Dist
  apply continuous_finsetSum
  intro k hk
  exact (continuous_const.sub (continuous_apply k)).abs

theorem continuous_contact_radius (X : Finset Point) (hne : X.Nonempty) :
    Continuous (contactRadius X hne) := by
  exact Continuous.finset_sup'_apply hne (fun x hx => continuous_contact_distance x)

/-- A minimizer of the full finite original-distance objective exists. The
compactness argument takes place in a coordinate box, independently of the
choice of a function-space norm. -/
theorem exists_contact_minimizer (X : Finset Point) (hne : X.Nonempty) :
    ∃ c : Point, ∀ m : Point, contactRadius X hne c ≤ contactRadius X hne m := by
  classical
  have hne' := hne
  obtain ⟨x₀, hx₀⟩ := hne'
  let R₀ := contactRadius X hne x₀
  have hR₀ : 0 ≤ R₀ := contact_radius_nonneg X hne x₀
  let a : Point := fun k => x₀ k - R₀
  let b : Point := fun k => x₀ k + R₀
  have hx₀box : x₀ ∈ Set.Icc a b := by
    constructor <;> intro k <;> dsimp [a, b] <;> linarith
  obtain ⟨c, hc, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
    ⟨x₀, hx₀box⟩ (continuous_contact_radius X hne).continuousOn
  refine ⟨c, fun m => ?_⟩
  by_cases hml : contactRadius X hne m ≤ R₀
  · have hmcoord (k : Fin 5) : |x₀ k - m k| ≤ R₀ :=
      (abs_coordinate_sub_le x₀ m k).trans
        ((contact_distance_le_radius X hne m x₀ hx₀).trans hml)
    have hmbox : m ∈ Set.Icc a b := by
      constructor
      · intro k
        have hk := (abs_le.mp (hmcoord k)).2
        dsimp [a]
        linarith
      · intro k
        have hk := (abs_le.mp (hmcoord k)).1
        dsimp [b]
        linarith
    exact hmin hmbox
  · exact (hmin hx₀box).trans (le_of_not_ge hml)

theorem signDot_smul (s v : Point) (t : ℝ) :
    signDot s (t • v) = t * signDot s v := by
  simp only [signDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem contact_form_motion (s x c v : Point) (t : ℝ) :
    signDot s (x - (c + t • v)) =
      signDot s (x - c) - t * signDot s v := by
  have hsplit : x - (c + t • v) = (x - c) - t • v := by
    ext k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  rw [hsplit, signDot_sub, signDot_smul]

/-- An elementary finite minimum of positive allowable step sizes. -/
theorem contact_common_step {ι : Type*} (u : Finset ι) (δ : ι → ℝ)
    (hδ : ∀ i ∈ u, 0 < δ i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ∈ u, t ≤ δ i := by
  classical
  revert hδ
  induction u using Finset.induction_on with
  | empty => intro hδ; exact ⟨1, by norm_num, by simp⟩
  | @insert i u hi ih =>
      intro hδ
      obtain ⟨t, ht, htu⟩ := ih (fun j hj => hδ j (Finset.mem_insert_of_mem hj))
      refine ⟨min (δ i) t, lt_min (hδ i (Finset.mem_insert_self _ _)) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (htu j hj)

/-- All finitely many affine forms decrease below the old radius when every
active form has a positive slope in the chosen direction. -/
theorem contact_strict_descent (X : Finset Point) (hne : X.Nonempty)
    (c v : Point)
    (hpos : ∀ x ∈ X, ∀ s : ContactSigns,
      signDot (contactSignVector s) (x - c) = contactRadius X hne c →
      0 < signDot (contactSignVector s) v) :
    ∃ m : Point, contactRadius X hne m < contactRadius X hne c := by
  classical
  let R := contactRadius X hne c
  let F : Finset (Point × ContactSigns) := X ×ˢ Finset.univ
  let f : Point × ContactSigns → ℝ := fun i =>
    signDot (contactSignVector i.2) (i.1 - c)
  let d : Point × ContactSigns → ℝ := fun i => signDot (contactSignVector i.2) v
  have hf (i : Point × ContactSigns) (hi : i ∈ F) : f i ≤ R := by
    exact (signDot_le_l1Dist _ _ _ (contactSignVector_isSign i.2)).trans
      (contact_distance_le_radius X hne c i.1 (Finset.mem_product.mp hi).1)
  let δ : Point × ContactSigns → ℝ := fun i =>
    if f i = R then 1 else (R - f i) / (2 * (|d i| + 1))
  have hδ (i : Point × ContactSigns) (hi : i ∈ F) : 0 < δ i := by
    dsimp [δ]
    split_ifs with heq
    · norm_num
    · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hf i hi) heq))
        (by have := abs_nonneg (d i); linarith)
  obtain ⟨t, ht, htδ⟩ := contact_common_step F δ hδ
  have hform (i : Point × ContactSigns) (hi : i ∈ F) : f i - t * d i < R := by
    by_cases heq : f i = R
    · have hd : 0 < d i := hpos i.1 (Finset.mem_product.mp hi).1 i.2 heq
      rw [heq]
      exact sub_lt_self R (mul_pos ht hd)
    · have hgap : 0 < R - f i := sub_pos.mpr (lt_of_le_of_ne (hf i hi) heq)
      have hden : 0 < 2 * (|d i| + 1) := by have := abs_nonneg (d i); linarith
      have hstep : t * (2 * (|d i| + 1)) ≤ R - f i := by
        exact (le_div_iff₀ hden).mp (by simpa [δ, heq] using htδ i hi)
      have habs : -|d i| ≤ d i := neg_abs_le (d i)
      have hm : -t * |d i| ≤ t * d i := by
        simpa using mul_le_mul_of_nonneg_left habs ht.le
      nlinarith [abs_nonneg (d i)]
  let m : Point := c + t • v
  refine ⟨m, ?_⟩
  apply (Finset.sup'_lt_iff hne).mpr
  intro x hx
  rw [← contact_norming_identity x m]
  have hi : (x, contactNormingSigns x m) ∈ F :=
    Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩
  simpa [m, f, d, R, contact_form_motion] using hform _ hi

noncomputable def contactActiveSigns (X : Finset Point) (hne : X.Nonempty)
    (c : Point) : Finset ContactSigns :=
  Finset.univ.filter (fun s => ∃ x ∈ X,
    signDot (contactSignVector s) (x - c) = contactRadius X hne c)

noncomputable def contactActiveVectors (X : Finset Point) (hne : X.Nonempty)
    (c : Point) : Finset Point :=
  (contactActiveSigns X hne c).image contactSignVector

theorem contactActiveVector_spec (X : Finset Point) (hne : X.Nonempty)
    (c s : Point) (hs : s ∈ contactActiveVectors X hne c) :
    IsSign s ∧ ∃ x ∈ X, signDot s (x - c) = contactRadius X hne c := by
  classical
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
  exact ⟨contactSignVector_isSign b, (Finset.mem_filter.mp hb).2⟩

theorem contactActiveVector_mem (X : Finset Point) (hne : X.Nonempty)
    (c x : Point) (hx : x ∈ X) (s : ContactSigns)
    (ha : signDot (contactSignVector s) (x - c) = contactRadius X hne c) :
    contactSignVector s ∈ contactActiveVectors X hne c := by
  classical
  exact Finset.mem_image.mpr ⟨s,
    Finset.mem_filter.mpr ⟨Finset.mem_univ s, x, hx, ha⟩, rfl⟩

/-- Every continuous linear separator on the coordinate space is represented
by the same explicit coordinate pairing used for the original sign forms. -/
theorem contact_dual_vector (f : Point →L[ℝ] ℝ) :
    ∃ v : Point, ∀ s : Point, signDot s v = f s := by
  classical
  let v : Point := fun k => f (Pi.single k (1 : ℝ))
  refine ⟨v, fun s => ?_⟩
  have hrepr : (∑ k, s k • Pi.single k (1 : ℝ)) = s := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  calc
    signDot s v = ∑ k, s k * f (Pi.single k (1 : ℝ)) := rfl
    _ = f (∑ k, s k • Pi.single k (1 : ℝ)) := by
      simp [map_sum, map_smul]
    _ = f s := congrArg f hrepr

/-- At a global finite l1 minimizer, zero belongs to the convex hull of its
actual active original sign forms. -/
theorem contact_active_convex_balance (X : Finset Point) (hne : X.Nonempty)
    (c : Point)
    (hmin : ∀ m : Point, contactRadius X hne c ≤ contactRadius X hne m) :
    (0 : Point) ∈ convexHull ℝ (contactActiveVectors X hne c : Set Point) := by
  classical
  by_contra hz
  obtain ⟨f, a, ha, hf⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (contactActiveVectors X hne c : Set Point))
    ((contactActiveVectors X hne c).finite_toSet.isClosed_convexHull ℝ) hz
  obtain ⟨v, hv⟩ := contact_dual_vector f
  have hpos : ∀ x ∈ X, ∀ s : ContactSigns,
      signDot (contactSignVector s) (x - c) = contactRadius X hne c →
      0 < signDot (contactSignVector s) v := by
    intro x hx s hs
    rw [hv]
    have hmem := contactActiveVector_mem X hne c x hx s hs
    have hsep := hf _ (subset_convexHull ℝ _ hmem)
    have hzero : f (0 : Point) = 0 := map_zero f
    linarith
  obtain ⟨m, hm⟩ := contact_strict_descent X hne c v hpos
  exact (not_lt_of_ge (hmin m)) hm

end Jung5
