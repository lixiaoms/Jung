import Jung.ContactExtraction
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace Jung

theorem half_weight_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (hp : 2 ≤ p) (u : Finset ι) (w : ι → ℝ)
    (hhalf : ∑ i ∈ u, w i = (1:ℝ)/2)
    (hsmall : ∀ i, w i < 1/(2*(p:ℝ)-2)) : p ≤ u.card := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < 2*(p:ℝ)-2 := by linarith
  by_contra hcard
  have hc : u.card ≤ p-1 := by omega
  have hu : u.Nonempty := by
    by_contra he
    have : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp [this] at hhalf
  have hlt := Finset.sum_lt_sum_of_nonempty hu (fun i hi => hsmall i)
  have hlt' : (1:ℝ)/2 < (u.card:ℝ)/(2*(p:ℝ)-2) := by
    convert hlt using 1
    · exact hhalf.symm
    · simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hc' : (u.card:ℝ) ≤ (p:ℝ)-1 := by
    have hc1 : u.card+1 ≤ p := by omega
    have : (u.card:ℝ)+1 ≤ p := by exact_mod_cast hc1
    linarith
  have hd := (lt_div_iff₀ hden).mp hlt'
  linarith

/-- A sign class with total weight one half has exactly p labels when the
two classes partition 2p labels and each individual weight is below 1/(2p-2). -/
theorem uniform_sign_balance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (hp : 2 ≤ p) (hcard : Fintype.card ι = 2*p)
    (s w : ι → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hsum : ∑ i, w i = 1) (hbal : ∑ i, w i*s i = 0)
    (hsmall : ∀ i, w i < 1/(2*(p:ℝ)-2)) : ∑ i, s i = 0 := by
  classical
  let u := Finset.univ.filter (fun i => s i = 1)
  have hterm (i : ι) : w i*s i = 2*(if s i=1 then w i else 0)-w i := by
    rcases hs i with h | h <;> norm_num [h] <;> ring
  have hu : ∑ i ∈ u, w i = (1:ℝ)/2 := by
    have hb : ∑ i, w i*s i = 2*(∑ i ∈ u, w i)-(∑ i, w i) := by
      simp_rw [hterm]
      simp [u, Finset.sum_filter, Finset.sum_sub_distrib, Finset.mul_sum]
    linarith
  have hv : ∑ i ∈ uᶜ, w i = (1:ℝ)/2 := by
    have heq := Finset.sum_add_sum_compl u w
    linarith
  have huc := half_weight_card p hp u w hu hsmall
  have hvc := half_weight_card p hp uᶜ w hv hsmall
  have hc : u.card = p := by
    have hcc : u.card + uᶜ.card = 2*p := by
      simpa [hcard] using Finset.card_add_card_compl u
    omega
  have hsign (i : ι) : s i = 2*(if s i=1 then (1:ℝ) else 0)-1 := by
    rcases hs i with h | h <;> norm_num [h]
  change (Finset.univ.filter (fun i => s i = 1)).card = p at hc
  rw [Finset.sum_congr rfl (fun i hi => hsign i)]
  simp [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter, hc,
    hcard, Nat.cast_mul]
  ring

theorem contacts_uniform {d n p : ℕ} (hp : 2 ≤ p) (hn : n=2*p)
    (y s : Fin n → Point d) (w : Fin n → ℝ)
    (c : Point d) (R : ℝ)
    (hs : ∀ i, IsSign (s i)) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1)
    (hbal : ∀ k, ∑ i, w i*s i k = 0)
    (hactive : ∀ i, signDot (s i) (y i-c) = R)
    (hdiam : ∀ i j, l1Dist (y i) (y j) ≤ 1)
    (hR : (2*(p:ℝ)-3)/(2*(p:ℝ)-2) < R) :
    ∀ m, 2*(p:ℝ)*R ≤ ∑ i, l1Dist (y i) m := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < 2*(p:ℝ)-2 := by linarith
  have hsmall (i : Fin n) : w i < 1/(2*(p:ℝ)-2) := by
    have hb := contact_weight_bound y s w c R hs hw hsum hbal hactive hdiam i
    have heq : 1-(2*(p:ℝ)-3)/(2*(p:ℝ)-2) = 1/(2*(p:ℝ)-2) := by
      apply (eq_div_iff hden.ne').mpr
      rw [sub_mul, div_mul_cancel₀ _ hden.ne']
      ring
    linarith
  have hu (k) : ∑ i, s i k = 0 :=
    uniform_sign_balance p hp (by simp [hn]) (fun i => s i k) w
      (fun i => hs i k) hsum (hbal k) hsmall
  intro m
  simpa [Nat.cast_mul,hn] using sum_contacts_lower_bound y s c R hs hu hactive m

end Jung
