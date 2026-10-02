import Jung.ContactCounting
import Mathlib.Data.Fin.Tuple.Sort

open scoped BigOperators

namespace Jung.Gap

def step {n : ℕ} (a : Fin (n+1) → ℝ) (r : Fin n) : ℝ :=
  a r.succ-a r.castSucc

def separates {n : ℕ} (r : Fin n) (i j : Fin (n+1)) : Prop :=
  (r.val < i.val ∧ ¬r.val < j.val) ∨ (r.val < j.val ∧ ¬r.val < i.val)

instance {n : ℕ} (r : Fin n) (i j : Fin (n+1)) : Decidable (separates r i j) := by
  unfold separates; infer_instance

def extend {n : ℕ} (a : Fin (n+1) → ℝ) (r : ℕ) : ℝ :=
  if h : r < n+1 then a ⟨r,h⟩ else 0

theorem gap_prefix {n : ℕ} (a : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    (∑ r : Fin n, if r.val < i.val then step a r else 0) = a i-a 0 := by
  classical
  let f : ℕ → ℝ := fun r => extend a (r+1)-extend a r
  have hf (r : Fin n) : f r.val = step a r := by
    simp [f, extend, step, show r.val+1<n+1 by omega, show r.val<n+1 by omega,
      Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]
  calc
    _ = ∑ r : Fin n, if r.val < i.val then f r.val else 0 := by
      simp_rw [hf]
    _ = ∑ r ∈ Finset.range n, if r < i.val then f r else 0 :=
      Fin.sum_univ_eq_sum_range (fun r => if r < i.val then f r else 0) n
    _ = ∑ r ∈ Finset.range i.val, f r := by
      have hsub : Finset.range i.val ⊆ Finset.range n :=
        Finset.range_mono (by omega)
      have heq := Finset.sum_subset hsub (f := fun r => if r < i.val then f r else 0)
        (by intro r hr hi; simp only [Finset.mem_range] at hi; simp [hi])
      rw [← heq]
      exact Finset.sum_congr rfl (fun r hr => if_pos (Finset.mem_range.mp hr))
    _ = extend a i.val-extend a 0 := Finset.sum_range_sub _ _
    _ = a i-a 0 := by simp [extend, i.isLt]

theorem ordered_pair {n : ℕ} (a : Fin (n+1) → ℝ) (ha : Monotone a)
    (i j : Fin (n+1)) :
    (∑ r : Fin n, if separates r i j then step a r else 0) = |a i-a j| := by
  classical
  wlog hij : i ≤ j generalizing i j
  · have hji : j ≤ i := le_of_not_ge hij
    rw [← abs_sub_comm]
    rw [← this j i hji]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [separates, or_comm]
  have hterm (r : Fin n) :
      (if separates r i j then step a r else 0) =
      (if r.val < j.val then step a r else 0)-(if r.val < i.val then step a r else 0) := by
    have hi : i.val ≤ j.val := hij
    by_cases hri : r.val < i.val <;> by_cases hrj : r.val < j.val
    all_goals simp [separates, hri, hrj]
    omega
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, gap_prefix, gap_prefix, abs_of_nonpos (sub_nonpos.mpr (ha hij))]
  ring

theorem step_nonneg {n : ℕ} (a : Fin (n+1) → ℝ) (ha : Monotone a)
    (r : Fin n) : 0 ≤ step a r := by
  exact sub_nonneg.mpr (ha (by change r.val ≤ r.val+1; omega))

def shore {n : ℕ} (r : Fin n) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun i => i.val ≤ r.val)

theorem card_shore {n : ℕ} (r : Fin n) : (shore r).card = r.val+1 := by
  classical
  let e : Fin (r.val+1) ↪ Fin (n+1) :=
    ⟨fun i => ⟨i.val, by omega⟩, by
      intro i j h
      apply Fin.ext
      exact congrArg (fun x : Fin (n+1) => x.val) h⟩
  have heq : shore r = Finset.univ.map e := by
    ext i
    simp only [shore, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hi
      exact ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    · rintro ⟨j, he⟩
      have hval : j.val = i.val := congrArg (fun x : Fin (n+1) => x.val) he
      omega
  rw [heq, Finset.card_map]
  simp

theorem separation_count {n p : ℕ} (hp : 1 ≤ p) (hn : n+1 = 2*p)
    (m : Fin (n+1)) (hm : m.val = p-1) (r : Fin n) :
    (∑ i : Fin (n+1), if separates r i m then (1:ℝ) else 0) =
      (min (r.val+1) (n-r.val) : ℕ) := by
  classical
  by_cases h : r.val < p-1
  · have heq (i : Fin (n+1)) : separates r i m ↔ i ∈ shore r := by
      simp only [separates, shore, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    simp_rw [heq]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hmin : min (r.val+1) (n-r.val) = r.val+1 := by omega
    rw [hmin, card_shore]
  · have heq (i : Fin (n+1)) : separates r i m ↔ i ∈ (shore r)ᶜ := by
      simp only [separates, shore, Finset.mem_compl, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    simp_rw [heq]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hmin : min (r.val+1) (n-r.val) = n-r.val := by omega
    rw [hmin, Finset.card_compl, Fintype.card_fin, card_shore]
    congr 1
    omega

theorem ordered_median {n p : ℕ} (hp : 1 ≤ p) (hn : n+1 = 2*p)
    (a : Fin (n+1) → ℝ) (ha : Monotone a)
    (m : Fin (n+1)) (hm : m.val = p-1) :
    (∑ i, |a i-a m|) = ∑ r : Fin n, step a r * (min (r.val+1) (n-r.val) : ℕ) := by
  classical
  simp_rw [← ordered_pair a ha]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have heq (i : Fin (n+1)) : (if separates r i m then step a r else 0) =
      step a r * (if separates r i m then (1:ℝ) else 0) := by
    split_ifs <;> simp
  simp_rw [heq]
  rw [← Finset.mul_sum, separation_count hp hn m hm r]

end Jung.Gap
