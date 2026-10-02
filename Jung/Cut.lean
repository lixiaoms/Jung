import Jung.CutAlgebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace Jung.Cut

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

noncomputable def indicator (S : Finset V) (i : V) : ℝ := if i ∈ S then 1 else 0

noncomputable def delta (S : Finset V) (i j : V) : ℝ :=
  indicator S i + indicator S j - 2*indicator S i*indicator S j

noncomputable def vector (S : Finset V) (i : V) : ℝ := 2*indicator S i-1

theorem indicator_sum (S : Finset V) : ∑ i, indicator S i = (S.card:ℝ) := by
  classical
  simp [indicator, ← Finset.sum_filter]

theorem vector_sum (S : Finset V) :
    ∑ i, vector S i = 2*(S.card:ℝ)-(Fintype.card V:ℝ) := by
  simp [vector, Finset.sum_sub_distrib, ← Finset.mul_sum, indicator_sum]

theorem vector_sign (S : Finset V) (i : V) : vector S i=1 ∨ vector S i = -1 := by
  classical
  by_cases hi : i ∈ S <;> norm_num [vector, indicator, hi]

theorem delta_ite (S : Finset V) (i j : V) : delta S i j =
    if ((i ∈ S ∧ j ∉ S) ∨ (j ∈ S ∧ i ∉ S)) then 1 else 0 := by
  classical
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> norm_num [delta, indicator, hi, hj]

theorem double_product (f g : V → ℝ) :
    (∑ i, ∑ j, f i*g j) = (∑ i, f i)*(∑ j, g j) := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem double_delta (S : Finset V) :
    (∑ i, ∑ j, delta S i j) = 2*(S.card:ℝ)*((Fintype.card V:ℝ)-S.card) := by
  simp only [delta, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, indicator_sum, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ]
  ring

theorem double_quadratic (S : Finset V) (v : V → ℝ) (hv : ∑ i, v i = 0) :
    (∑ i, ∑ j, v i*delta S i j*v j) = -2*(∑ i, v i*indicator S i)^2 := by
  have ht (i j : V) : v i*delta S i j*v j =
      (v i*indicator S i)*v j + v i*(v j*indicator S j) -
        2*((v i*indicator S i)*(v j*indicator S j)) := by unfold delta; ring
  have hthird : (∑ i, ∑ j, 2*((v i*indicator S i)*(v j*indicator S j))) =
      2*(∑ i, v i*indicator S i)^2 := by
    calc
      _ = 2*(∑ i, ∑ j, (v i*indicator S i)*(v j*indicator S j)) := by
        simp only [Finset.mul_sum]
      _ = _ := by rw [double_product]; ring
  simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hthird, double_product, double_product, hv]
  ring

theorem intersection_dot (A C : Finset V) :
    (∑ i, vector C i*indicator A i) = 2*((A∩C).card:ℝ)-(A.card:ℝ) := by
  classical
  have ht (i : V) : vector C i*indicator A i =
      2*indicator (A∩C) i-indicator A i := by
    by_cases ha : i∈A <;> by_cases hc : i∈C <;> norm_num [vector, indicator, ha, hc]
  simp_rw [ht]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, indicator_sum]

theorem odd_square (p t : ℕ) (hp : Odd p) :
    (1:ℝ) ≤ (2*(t:ℝ)-(p:ℝ))^2 := by
  have hn : (2*(t:ℤ)-(p:ℤ)) ≠ 0 := by
    obtain ⟨r,hr⟩ := hp
    omega
  have hs : (1:ℤ) ≤ (2*(t:ℤ)-(p:ℤ))^2 := by
    have hcases : 2*(t:ℤ)-(p:ℤ) ≤ -1 ∨ 1 ≤ 2*(t:ℤ)-(p:ℤ) := by omega
    rcases hcases with h | h <;> nlinarith
  exact_mod_cast hs

noncomputable def distance (S : I → Finset V) (w : I → ℝ) (i j : V) : ℝ :=
  ∑ a, w a*delta (S a) i j

noncomputable def total (S : I → Finset V) (w : I → ℝ) : ℝ :=
  (∑ i, ∑ j, distance S w i j)/2

noncomputable def quadratic (S : I → Finset V) (w : I → ℝ) (C : Finset V) : ℝ :=
  ∑ a, w a*(∑ i, vector C i*indicator (S a) i)^2

theorem sum_switch (f : I → V → V → ℝ) :
    (∑ i, ∑ j, ∑ a, f a i j) = ∑ a, ∑ i, ∑ j, f a i j := by
  calc
    _ = ∑ i, ∑ a, ∑ j, f a i j := by
      apply Finset.sum_congr rfl; intro i hi; exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem total_formula (S : I → Finset V) (w : I → ℝ) :
    total S w = ∑ a, w a*(S a).card*((Fintype.card V:ℝ)-(S a).card) := by
  unfold total distance
  rw [sum_switch]
  simp_rw [← Finset.mul_sum, double_delta]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem quadratic_formula (S : I → Finset V) (w : I → ℝ) (C : Finset V)
    (hc : ∑ i, vector C i = 0) :
    (∑ i, ∑ j, vector C i*distance S w i j*vector C j) = -2*quadratic S w C := by
  unfold distance quadratic
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [sum_switch]
  have ht (a : I) : (∑ i, ∑ j, vector C i*(w a*delta (S a) i j)*vector C j) =
      w a*(∑ i, ∑ j, vector C i*delta (S a) i j*vector C j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [ht, double_quadratic _ _ hc]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem quadratic_upper (p : ℕ) (hcard : Fintype.card V = 2*p)
    (S : I → Finset V) (w : I → ℝ) (C : Finset V) (hC : C.card = p)
    (hd : ∀ i j, distance S w i j ≤ 1) :
    total S w + quadratic S w C ≤ 2*(p:ℝ)^2 := by
  have hc : ∑ i, vector C i = 0 := by rw [vector_sum,hC,hcard]; push_cast; ring
  have hnonneg (i j : V) : 0 ≤ 1-vector C i*vector C j := by
    rcases vector_sign C i with hi | hi <;> rcases vector_sign C j with hj | hj
    all_goals norm_num [hi,hj]
  have hle := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) =>
      mul_le_mul_of_nonneg_left (hd i j) (hnonneg i j)))
  have hl : (∑ i, ∑ j, (1-vector C i*vector C j)*distance S w i j) =
      2*(total S w+quadratic S w C) := by
    have ht (i j : V) : (1-vector C i*vector C j)*distance S w i j =
        distance S w i j-vector C i*distance S w i j*vector C j := by ring
    simp_rw [ht, Finset.sum_sub_distrib]
    rw [quadratic_formula S w C hc]
    unfold total
    ring
  have hr : (∑ i, ∑ j, (1-vector C i*vector C j)*1) = 4*(p:ℝ)^2 := by
    simp only [mul_one, Finset.sum_sub_distrib]
    rw [double_product, hc]
    simp [hcard, Nat.cast_mul]
    ring
  rw [hl,hr] at hle
  linarith

noncomputable def size (S : Finset V) : ℕ := min S.card (Fintype.card V-S.card)

noncomputable def objective (S : I → Finset V) (w : I → ℝ) : ℝ :=
  ∑ a, w a*(size (S a):ℝ)

noncomputable def balanced (p : ℕ) (S : I → Finset V) (w : I → ℝ) : Finset I :=
  Finset.univ.filter (fun a => (S a).card=p ∧ w a≠0)

theorem size_facts (p : ℕ) (hc : Fintype.card V=2*p) (S : Finset V) :
    size S ≤ p ∧ (size S=p ↔ S.card=p) ∧
    (S.card:ℝ)*((2*p:ℝ)-S.card) = (size S:ℝ)*((2*p:ℝ)-size S) := by
  have hb := S.card_le_univ
  unfold size
  rw [hc] at hb ⊢
  constructor
  · omega
  constructor
  · omega
  · by_cases h : S.card ≤ p
    · have hm : min S.card (2*p-S.card)=S.card := by omega
      rw [hm]
    · have hm : min S.card (2*p-S.card)=2*p-S.card := by omega
      rw [hm, Nat.cast_sub (by omega)]
      push_cast
      ring

theorem balanced_sum (p : ℕ) (S : I → Finset V) (w : I → ℝ) :
    (∑ a ∈ balanced p S w, w a) = ∑ a, if (S a).card=p then w a else 0 := by
  classical
  simp only [balanced, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hc : (S a).card=p <;> by_cases hw : w a=0 <;> simp [hc,hw]

theorem basic_moments (p : ℕ) (hc : Fintype.card V=2*p)
    (S : I → Finset V) (w : I → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (p+1:ℝ)*objective S w-(p:ℝ)*(∑ a ∈ balanced p S w,w a) ≤ total S w ∧
    (p:ℝ)*(∑ a ∈ balanced p S w,w a) ≤ objective S w := by
  classical
  have hbasic (a : I) : (p+1:ℝ)*(w a*(size (S a):ℝ))-
      (p:ℝ)*(if (S a).card=p then w a else 0) ≤
      w a*(S a).card*((2*p:ℝ)-(S a).card) := by
    obtain ⟨hs,heq,hprod⟩ := size_facts p hc (S a)
    have hnum : (p+1:ℝ)*(size (S a):ℝ)-
        (p:ℝ)*(if (S a).card=p then 1 else 0) ≤
        (size (S a):ℝ)*((2*p:ℝ)-size (S a)) := by
      by_cases ha : (S a).card=p
      · rw [if_pos ha, heq.mpr ha]
        nlinarith
      · have hsreal : (size (S a):ℝ) ≤ (p:ℝ)-1 := by
          have hnat : size (S a)+1 ≤ p := by omega
          have : (size (S a):ℝ)+1 ≤ p := by exact_mod_cast hnat
          linarith
        rw [if_neg ha]
        nlinarith [show (0:ℝ) ≤ size (S a) by positivity]
    have hm := mul_le_mul_of_nonneg_left hnum (hw a)
    rw [← hprod] at hm
    convert hm using 1 <;> (try split_ifs) <;> ring
  have hweight (a : I) : (p:ℝ)*(if (S a).card=p then w a else 0) ≤
      w a*(size (S a):ℝ) := by
    obtain ⟨hs,heq,hprod⟩ := size_facts p hc (S a)
    by_cases ha : (S a).card=p
    · rw [if_pos ha,heq.mpr ha]; nlinarith
    · rw [if_neg ha, mul_zero]; exact mul_nonneg (hw a) (Nat.cast_nonneg _)
  constructor
  · rw [total_formula,balanced_sum]
    unfold objective
    have hh := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => hbasic a)
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat, hc] using hh
  · rw [balanced_sum]
    unfold objective
    simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => hweight a)

theorem quadratic_lower (p : ℕ) (hp : Odd p) (hc : Fintype.card V=2*p)
    (S : I → Finset V) (w : I → ℝ) (hw : ∀ a,0 ≤ w a)
    (c : I) (hcB : c∈balanced p S w) :
    (∑ a ∈ balanced p S w,w a)+((p:ℝ)^2-1)*w c ≤ quadratic S w (S c) := by
  classical
  have hcsize : (S c).card=p := (Finset.mem_filter.mp hcB).2.1
  have hdot (a : I) (ha : a∈balanced p S w) :
      (if a=c then (p:ℝ)^2 else 1) ≤ (∑ i,vector (S c) i*indicator (S a) i)^2 := by
    have hasize : (S a).card=p := (Finset.mem_filter.mp ha).2.1
    rw [intersection_dot]
    by_cases hac : a=c
    · subst a
      simp [hcsize]
      nlinarith
    · rw [if_neg hac,hasize]
      exact odd_square p ((S a∩S c).card) hp
  have hl := Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hdot a ha) (hw a))
  have hsub : (∑ a ∈ balanced p S w,w a*(∑ i,vector (S c) i*indicator (S a) i)^2) ≤
      quadratic S w (S c) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a ha hnot => mul_nonneg (hw a) (sq_nonneg _))
  have hid : (∑ a ∈ balanced p S w,w a*(if a=c then (p:ℝ)^2 else 1)) =
      (∑ a ∈ balanced p S w,w a)+((p:ℝ)^2-1)*w c := by
    have ht (a : I) : w a*(if a=c then (p:ℝ)^2 else 1) =
        w a+(if a=c then ((p:ℝ)^2-1)*w c else 0) := by
      by_cases h : a=c <;> simp [h] <;> ring
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp [hcB]
  rw [hid] at hl
  exact hl.trans hsub

theorem weight_bound (p : ℕ) (hp3 : 3 ≤ p) (hp : Odd p) (hc : Fintype.card V=2*p)
    (S : I → Finset V) (w : I → ℝ) (hw : ∀ a,0 ≤ w a)
    (hd : ∀ i j,distance S w i j ≤ 1)
    (hcount : (balanced p S w).card ≤ 2*p-1) :
    objective S w ≤ Jung.cutBound p := by
  classical
  let B := balanced p S w
  let W : ℝ := ∑ a∈B,w a
  have hW : 0 ≤ W := Finset.sum_nonneg (fun a ha => hw a)
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp3
  have hden : 0 < 2*(p:ℝ)-1 := by linarith
  have hkey : total S w+Jung.cutCoefficient p*W ≤ 2*(p:ℝ)^2 := by
    by_cases hzero : W=0
    · rw [hzero,mul_zero,add_zero]
      have htotal := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
        Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hd i j))
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hc,
        Nat.cast_mul, Nat.cast_ofNat] at htotal
      unfold total
      nlinarith
    · have hB : B.Nonempty := by
        by_contra hn
        have he : B=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        simp [W,he] at hzero
      obtain ⟨c,hcB,hmax⟩ := Finset.exists_max_image B w hB
      have hsum : W ≤ (B.card:ℝ)*w c := by
        simpa [W,nsmul_eq_mul] using B.sum_le_card_nsmul w (w c) hmax
      have hcountR : (B.card:ℝ) ≤ 2*(p:ℝ)-1 := by
        have hn : B.card+1 ≤ 2*p := by dsimp [B]; omega
        have : (B.card:ℝ)+1 ≤ 2*(p:ℝ) := by exact_mod_cast hn
        linarith
      have hmaxW : W ≤ (2*(p:ℝ)-1)*w c :=
        hsum.trans (mul_le_mul_of_nonneg_right hcountR (hw c))
      have hl := quadratic_lower p hp hc S w hw c hcB
      have hu := quadratic_upper p hc S w (S c) (Finset.mem_filter.mp hcB).2.1 hd
      have hcoef : Jung.cutCoefficient (p:ℝ)*(2*(p:ℝ)-1) =
          (2*(p:ℝ)-1)+((p:ℝ)^2-1) := by
        unfold Jung.cutCoefficient
        rw [add_mul,div_mul_cancel₀ _ hden.ne']
        ring
      have hs := mul_le_mul_of_nonneg_left hmaxW (show 0 ≤ (p:ℝ)^2-1 by nlinarith)
      have heq := congrArg (fun z : ℝ => z*W) hcoef
      dsimp [W] at *
      nlinarith
  obtain ⟨hb,hwgt⟩ := basic_moments p hc S w hw
  exact Jung.cut_bound_of_moments p (total S w) W (objective S w) hpR hb hwgt hkey

end Jung.Cut
