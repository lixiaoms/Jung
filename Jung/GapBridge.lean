import Jung.Gap
import Jung.Cut
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Tauto

open scoped BigOperators

namespace Jung.Gap

variable {n d : ℕ}

noncomputable def order (x : Fin (n+1) → Point d) (k : Fin d) : Equiv.Perm (Fin (n+1)) :=
  Tuple.sort (fun i => x i k)

noncomputable def ordered (x : Fin (n+1) → Point d) (k : Fin d) (i : Fin (n+1)) : ℝ :=
  x (order x k i) k

theorem ordered_monotone (x : Fin (n+1) → Point d) (k : Fin d) : Monotone (ordered x k) :=
  Tuple.monotone_sort (fun i => x i k)

noncomputable def cut (x : Fin (n+1) → Point d) (a : Fin d × Fin n) : Finset (Fin (n+1)) :=
  (shore a.2).map (order x a.1).toEmbedding

noncomputable def weight (x : Fin (n+1) → Point d) (a : Fin d × Fin n) : ℝ :=
  step (ordered x a.1) a.2

noncomputable def median (x : Fin (n+1) → Point d) (m : Fin (n+1)) : Point d :=
  fun k => ordered x k m

theorem cut_card (x : Fin (n+1) → Point d) (a : Fin d × Fin n) :
    (cut x a).card = a.2.val+1 := by rw [cut,Finset.card_map,card_shore]

theorem cut_mem (x : Fin (n+1) → Point d) (a : Fin d × Fin n) (i : Fin (n+1)) :
    i∈cut x a ↔ (order x a.1).symm i ∈ shore a.2 := by
  simp [cut, Equiv.eq_symm_apply]

theorem cut_delta (x : Fin (n+1) → Point d) (a : Fin d × Fin n) (i j : Fin (n+1)) :
    Cut.delta (cut x a) i j =
      if separates a.2 ((order x a.1).symm i) ((order x a.1).symm j) then 1 else 0 := by
  classical
  rw [Cut.delta_ite]
  simp only [cut_mem,shore,Finset.mem_filter,Finset.mem_univ,true_and,separates]
  congr 1
  simp only [not_lt,not_le]
  apply propext
  tauto

theorem weight_nonneg (x : Fin (n+1) → Point d) (a : Fin d × Fin n) : 0 ≤ weight x a :=
  step_nonneg _ (ordered_monotone x a.1) a.2

theorem weight_distance (x : Fin (n+1) → Point d) (i j : Fin (n+1)) :
    Cut.distance (cut x) (weight x) i j = l1Dist (x i) (x j) := by
  classical
  unfold Cut.distance
  rw [Fintype.sum_prod_type]
  unfold l1Dist
  apply Finset.sum_congr rfl
  intro k hk
  simp only [cut_delta,weight,mul_ite,mul_one,mul_zero]
  rw [ordered_pair _ (ordered_monotone x k)]
  simp [ordered]

theorem cut_size (x : Fin (n+1) → Point d) (a : Fin d × Fin n) :
    Cut.size (cut x a) = min (a.2.val+1) (n-a.2.val) := by
  unfold Cut.size
  rw [cut_card,Fintype.card_fin]
  congr 1
  omega

theorem weight_objective (p : ℕ) (hp : 1 ≤ p) (hn : n+1=2*p)
    (x : Fin (n+1) → Point d) (m : Fin (n+1)) (hm : m.val=p-1) :
    Cut.objective (cut x) (weight x) = ∑ i,l1Dist (x i) (median x m) := by
  unfold Cut.objective
  rw [Fintype.sum_prod_type]
  simp only [weight,cut_size]
  unfold l1Dist
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← ordered_median hp hn _ (ordered_monotone x k) m hm]
  exact Equiv.sum_comp (order x k) (fun i => |x i k-median x m k|)

theorem balanced_card (p : ℕ) (hp : 2 ≤ p) (hn : n+1=2*p)
    (x : Fin (n+1) → Point d) : (Cut.balanced p (cut x) (weight x)).card ≤ d := by
  classical
  let r : Fin n := ⟨p-1,by omega⟩
  have hsub : Cut.balanced p (cut x) (weight x) ⊆
      Finset.univ.image (fun k : Fin d => (k,r)) := by
    intro a ha
    have hcard : (cut x a).card=p := (Finset.mem_filter.mp ha).2.1
    rw [cut_card] at hcard
    have hr : a.2=r := Fin.ext (by dsimp [r]; omega)
    exact Finset.mem_image.mpr ⟨a.1,Finset.mem_univ _,Prod.ext rfl hr.symm⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans_eq (by simp))

end Jung.Gap

namespace Jung

theorem median_bound {n d p : ℕ} (hp3 : 3 ≤ p) (hp : Odd p) (hn : n+1=2*p)
    (hd : d ≤ 2*p-1) (x : Fin (n+1) → Point d)
    (hdiam : ∀ i j,l1Dist (x i) (x j) ≤ 1) :
    ∃ m : Point d, (∑ i,l1Dist (x i) m) ≤ cutBound p := by
  let mid : Fin (n+1) := ⟨p-1,by omega⟩
  refine ⟨Gap.median x mid,?_⟩
  rw [← Gap.weight_objective p (by omega) hn x mid rfl]
  apply Cut.weight_bound p hp3 hp (by simp [hn]) (Gap.cut x) (Gap.weight x)
    (Gap.weight_nonneg x)
  · intro i j
    rw [Gap.weight_distance]
    exact hdiam i j
  · exact (Gap.balanced_card p (by omega) hn x).trans hd

end Jung
