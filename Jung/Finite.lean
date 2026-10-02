import Jung.GapBridge
import Jung.Extension

open scoped BigOperators

namespace Jung

noncomputable def coefficient (k : ℕ) : ℝ := (4*(k:ℝ)-1)/(4*(k:ℝ))

theorem coefficient_nonneg (k : ℕ) (hk : 1 ≤ k) : 0 ≤ coefficient k := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  unfold coefficient
  exact div_nonneg (by linarith) (by linarith)

theorem unit_finite_enclosing (k : ℕ) (hk : 2 ≤ k) :
    UnitFiniteEnclosing (4*k+1) (coefficient k) := by
  classical
  intro X hne hdiam
  obtain ⟨c,hmin⟩ := exists_contact_minimizer X hne
  by_cases hR : contactRadius X hne c ≤ coefficient k
  · exact ⟨c,fun x hx => (contact_distance_le_radius X hne c x hx).trans hR⟩
  · obtain ⟨y,s,w,hy,hs,hw,hsum,hbal,hactive⟩ := contact_active_family X hne c hmin
    let p := 2*k+1
    have hp5 : 5 ≤ p := by dsimp [p]; omega
    have hpodd : Odd p := ⟨k,rfl⟩
    have hn : (4*k+1)+1=2*p := by dsimp [p]; omega
    have hd : 4*k+1 ≤ 2*p-1 := by dsimp [p]; omega
    have hpR : (5:ℝ) ≤ p := by exact_mod_cast hp5
    have hcoef : coefficient k = (2*(p:ℝ)-3)/(2*(p:ℝ)-2) := by
      unfold coefficient p
      push_cast
      congr 1 <;> ring
    have hdiamY (i j) : l1Dist (y i) (y j) ≤ 1 := hdiam (y i) (hy i) (y j) (hy j)
    obtain ⟨m,hm⟩ := median_bound (by omega) hpodd hn hd y hdiamY
    have hl := contacts_uniform (by omega : 2 ≤ p) hn y s w c
      (contactRadius X hne c) hs hw hsum hbal hactive hdiamY
      (by rw [← hcoef]; exact lt_of_not_ge hR) m
    have hb := cut_bound_strict (p:ℝ) hpR
    have hp0 : 0 < 2*(p:ℝ) := by linarith
    have hrad : coefficient k < contactRadius X hne c := lt_of_not_ge hR
    rw [hcoef] at hrad
    have hmultip := mul_lt_mul_of_pos_left hrad hp0
    nlinarith

theorem jung_l1_four_k_plus_one (k : ℕ) (hk : 2 ≤ k)
    (X : Set (Point (4*k+1))) (hne : X.Nonempty) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ x∈X,∀ y∈X,l1Dist x y ≤ D) :
    ∃ c : Point (4*k+1),∀ x∈X,l1Dist x c ≤ coefficient k*D :=
  enclosing_all_sets_of_unit_finite (coefficient_nonneg k (by omega))
    (unit_finite_enclosing k hk) X hne D hD hdiam

end Jung
