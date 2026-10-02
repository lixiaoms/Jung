import Jung5.Gap
import Jung5.Certificates
import Mathlib.Tactic.Tauto

/-!
Aggregate the twenty-five genuine scalar coordinate gaps into canonical
unoriented cuts. All labels are retained, and zero gap lengths are permitted.
-/

open scoped BigOperators

namespace Jung5
namespace Gap
noncomputable section

/-- Orient a cut by the unique shore which omits label zero. -/
def canonical (s : Finset (Fin 6)) : Cut :=
  if h : (0 : Fin 6) ∈ s then ⟨sᶜ, by simp [h]⟩ else ⟨s, h⟩

theorem canonical_separates (s : Finset (Fin 6)) (i j : Fin 6) :
    separates (canonical s) i j ↔
      ((i ∈ s ∧ j ∉ s) ∨ (j ∈ s ∧ i ∉ s)) := by
  classical
  unfold canonical
  split_ifs <;> simp only [separates, Finset.mem_compl] <;> tauto

def canonicalPrefix (e : Equiv.Perm (Fin 6)) (r : Fin 5) : Cut :=
  canonical (rawPrefix e r)

theorem canonicalPrefix_separates (e : Equiv.Perm (Fin 6))
    (r : Fin 5) (i j : Fin 6) :
    separates (canonicalPrefix e r) i j ↔
      rankSeparates r (e.symm i) (e.symm j) := by
  rw [canonicalPrefix, canonical_separates]
  simp only [mem_rawPrefix, rankSeparates]

theorem canonicalPrefix_minShore (e : Equiv.Perm (Fin 6)) (r : Fin 5) :
    minShore (canonicalPrefix e r) = gapCost r := by
  classical
  have hr := r.isLt
  unfold canonicalPrefix canonical
  split_ifs
  all_goals
    simp only [minShore, Finset.card_compl, Fintype.card_fin, card_rawPrefix, gapCost]
    omega

/-- Only the central rank cut can have three labels on each side. -/
theorem canonicalPrefix_balanced (e : Equiv.Perm (Fin 6)) (r : Fin 5)
    (h : (canonicalPrefix e r).val.card = 3) : r = 2 := by
  have hm : minShore (canonicalPrefix e r) = 3 := by
    simp only [minShore, h]
    decide
  rw [canonicalPrefix_minShore] at hm
  have hr := r.isLt
  apply Fin.ext
  change r.val = 2
  unfold gapCost at hm
  omega

/-- Sorting is on the original six coordinate values, with labels as tie-breaks. -/
def coordOrder (p : Fin 6 → Point) (k : Fin 5) : Equiv.Perm (Fin 6) :=
  Tuple.sort (fun i => p i k)

def orderedCoord (p : Fin 6 → Point) (k : Fin 5) (i : Fin 6) : ℝ :=
  p (coordOrder p k i) k

theorem orderedCoord_monotone (p : Fin 6 → Point) (k : Fin 5) :
    Monotone (orderedCoord p k) :=
  Tuple.monotone_sort (fun i => p i k)

def coordGap (p : Fin 6 → Point) (k r : Fin 5) : ℝ :=
  stepGap (orderedCoord p k) r

def coordCut (p : Fin 6 → Point) (k r : Fin 5) : Cut :=
  canonicalPrefix (coordOrder p k) r

/-- A concrete ambient center, taking the lower median in every coordinate. -/
def median (p : Fin 6 → Point) : Point := fun k => orderedCoord p k 2

theorem coordGap_nonneg (p : Fin 6 → Point) (k r : Fin 5) :
    0 ≤ coordGap p k r :=
  stepGap_nonneg _ (orderedCoord_monotone p k) r

theorem coord_pair (p : Fin 6 → Point) (k : Fin 5) (i j : Fin 6) :
    (∑ r : Fin 5, if separates (coordCut p k r) i j
      then coordGap p k r else 0) = |p i k - p j k| := by
  classical
  simp only [coordCut, canonicalPrefix_separates, coordGap]
  rw [ordered_pair _ (orderedCoord_monotone p k)]
  simp [orderedCoord]

theorem coord_median (p : Fin 6 → Point) (k : Fin 5) :
    (∑ i : Fin 6, |p i k - median p k|) =
      ∑ r : Fin 5, coordGap p k r * (gapCost r : ℝ) := by
  classical
  calc
    _ = ∑ i : Fin 6, |orderedCoord p k i - orderedCoord p k 2| := by
      symm
      exact Equiv.sum_comp (coordOrder p k) (fun i => |p i k - median p k|)
    _ = _ := ordered_median _ (orderedCoord_monotone p k)

/-- Aggregate equal canonical cuts over all actual coordinate gaps. -/
def weight (p : Fin 6 → Point) (c : Cut) : ℝ :=
  ∑ k : Fin 5, ∑ r : Fin 5, if c = coordCut p k r then coordGap p k r else 0

theorem weight_nonneg (p : Fin 6 → Point) (c : Cut) : 0 ≤ weight p c := by
  classical
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro r hr
  split_ifs
  · exact coordGap_nonneg p k r
  · exact le_rfl

/-- Finite regrouping by the exact cut identity; no cuts are discarded. -/
theorem weight_eval (p : Fin 6 → Point) (f : Cut → ℝ) :
    (∑ c : Cut, weight p c * f c) =
      ∑ k : Fin 5, ∑ r : Fin 5, coordGap p k r * f (coordCut p k r) := by
  classical
  unfold weight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp [ite_mul]

/-- All pairwise distances are exactly those of the original real points. -/
theorem weight_distance (p : Fin 6 → Point) (i j : Fin 6) :
    (∑ c : Cut, if separates c i j then weight p c else 0) =
      l1Dist (p i) (p j) := by
  classical
  calc
    _ = ∑ c : Cut, weight p c * (if separates c i j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : separates c i j <;> simp [h]
    _ = ∑ k : Fin 5, ∑ r : Fin 5,
        coordGap p k r * (if separates (coordCut p k r) i j then 1 else 0) :=
      weight_eval p _
    _ = l1Dist (p i) (p j) := by
      unfold l1Dist
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [mul_ite, mul_one, mul_zero] using coord_pair p k i j

/-- The weighted cut objective is the sum of six distances to the actual median. -/
theorem weight_objective (p : Fin 6 → Point) :
    (∑ c : Cut, weight p c * (minShore c : ℝ)) =
      ∑ i : Fin 6, l1Dist (p i) (median p) := by
  rw [weight_eval]
  simp only [coordCut, canonicalPrefix_minShore]
  symm
  unfold l1Dist
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  exact coord_median p k

/-- A supported balanced cut must come from one of the five central gaps. -/
theorem balancedSupport_subset (p : Fin 6 → Point) :
    balancedSupport (weight p) ⊆
      Finset.univ.image (fun k : Fin 5 => coordCut p k 2) := by
  classical
  intro c hc
  simp only [balancedSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  by_contra hnot
  have hz : weight p c = 0 := by
    unfold weight
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro r hr
    split_ifs with heq
    · have hcard : (canonicalPrefix (coordOrder p k) r).val.card = 3 := by
        change (coordCut p k r).val.card = 3
        rw [← heq]
        exact hc.1
      have hcentral : r = 2 := canonicalPrefix_balanced _ _ hcard
      subst r
      exact False.elim (hnot (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, heq.symm⟩))
    · rfl
  exact hc.2 hz

theorem balancedSupport_card (p : Fin 6 → Point) :
    (balancedSupport (weight p)).card ≤ 5 := by
  classical
  calc
    _ ≤ (Finset.univ.image (fun k : Fin 5 => coordCut p k 2)).card :=
      Finset.card_le_card (balancedSupport_subset p)
    _ ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
    _ = 5 := by simp

end
end Gap

/-- Six arbitrary real points of pairwise Manhattan distance at most one have
an ambient center whose sum of their six distances is at most `9 / 2`.
The coordinate sorting and cut representation allow repeated points and ties. -/
theorem six_point_median_bound (p : Fin 6 → Point)
    (hdiam : ∀ i j, l1Dist (p i) (p j) ≤ 1) :
    ∃ m : Point, (∑ i : Fin 6, l1Dist (p i) m) ≤ (9 : ℝ) / 2 := by
  refine ⟨Gap.median p, ?_⟩
  rw [← Gap.weight_objective p]
  apply cut_weight_bound (Gap.weight p) (Gap.weight_nonneg p)
  · intro i j
    rw [Gap.weight_distance p i j]
    exact hdiam i j
  · exact Gap.balancedSupport_card p

end Jung5
