import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Jung5.CertificateData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Jung5

/-- A canonical unoriented cut: choose its shore not containing vertex zero. -/
abbrev Cut := {s : Finset (Fin 6) // (0 : Fin 6) ∉ s}

def minShore (c : Cut) : ℕ :=
  min c.val.card (6 - c.val.card)

def separates (c : Cut) (i j : Fin 6) : Prop :=
  (i ∈ c.val ∧ j ∉ c.val) ∨ (j ∈ c.val ∧ i ∉ c.val)

instance (c : Cut) (i j : Fin 6) : Decidable (separates c i j) := by
  unfold separates
  infer_instance

noncomputable def balancedSupport (w : Cut → ℝ) : Finset Cut := by
  classical
  exact Finset.univ.filter (fun c => c.val.card = 3 ∧ w c ≠ 0)

namespace CutCertificate

abbrev Edge := Fin 15

def balancedCut (i : Fin 10) : Cut :=
  ⟨CertificateData.balancedShore i, by fin_cases i <;> decide⟩

theorem balancedCut_card (i : Fin 10) : (balancedCut i).val.card = 3 := by
  fin_cases i <;> decide

theorem balancedCut_injective : Function.Injective balancedCut := by decide

theorem balancedCut_coverage :
    ∀ c : Cut, c.val.card = 3 → ∃ i : Fin 10, balancedCut i = c := by decide

def supportCode (s : Finset (Fin 10)) : ℕ := ∑ i ∈ s, 2 ^ i.val

def coefficient (s : Finset (Fin 10)) (e : Edge) : ℕ :=
  CertificateData.weight (supportCode s) e

def capacity (s : Finset (Fin 10)) (c : Cut) : ℕ :=
  ∑ e : Edge, if separates c (CertificateData.pairEndpoints e).1
    (CertificateData.pairEndpoints e).2 then coefficient s e else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The finite witnesses are checked by kernel reduction, not an external oracle. -/
theorem finite_certificate :
    ∀ s : Finset (Fin 10), s.card ≤ 5 →
      (∑ e : Edge, coefficient s e) ≤ 270 ∧
      ∀ c : Cut,
        (c.val.card ≠ 3 ∨ ∃ i ∈ s, balancedCut i = c) →
        60 * minShore c ≤ capacity s c := by
  decide

end CutCertificate

open CutCertificate

theorem cut_weight_bound (w : Cut → ℝ) (hw : ∀ c, 0 ≤ w c)
    (hdiam : ∀ i j,
      (∑ c : Cut, if separates c i j then w c else 0) ≤ 1)
    (hsupport : (balancedSupport w).card ≤ 5) :
    (∑ c : Cut, w c * (minShore c : ℝ)) ≤ 9 / 2 := by
  classical
  let s : Finset (Fin 10) := Finset.univ.filter (fun i => w (balancedCut i) ≠ 0)
  have himage : s.image balancedCut ⊆ balancedSupport w := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, balancedCut_card i, (Finset.mem_filter.mp hi).2⟩
  have hs : s.card ≤ 5 := calc
    s.card = (s.image balancedCut).card :=
      (Finset.card_image_of_injective s balancedCut_injective).symm
    _ ≤ (balancedSupport w).card := Finset.card_le_card himage
    _ ≤ 5 := hsupport
  obtain ⟨hTotal, hCap⟩ := finite_certificate s hs
  let q : Edge → ℝ := fun e => (coefficient s e : ℝ) / 60
  have hq_nonneg (e : Edge) : 0 ≤ q e := by
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have htotal_real : (∑ e : Edge, (coefficient s e : ℝ)) ≤ 270 := by
    exact_mod_cast hTotal
  have hq_total : (∑ e : Edge, q e) ≤ 9 / 2 := by
    calc
      (∑ e : Edge, q e) = (∑ e : Edge, (coefficient s e : ℝ)) / 60 := by
        simp only [q, div_eq_mul_inv, Finset.sum_mul]
      _ ≤ 270 / 60 := div_le_div_of_nonneg_right htotal_real (by norm_num)
      _ = 9 / 2 := by norm_num
  have capacity_eq (c : Cut) :
      (∑ e : Edge, if separates c (CertificateData.pairEndpoints e).1
        (CertificateData.pairEndpoints e).2 then q e else 0) =
        (capacity s c : ℝ) / 60 := by
    simp only [capacity, Nat.cast_sum]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h : separates c (CertificateData.pairEndpoints e).1
      (CertificateData.pairEndpoints e).2
    · simp [h, q, div_eq_mul_inv]
    · simp [h]
  have hcapacity (c : Cut) (hc : w c ≠ 0) :
      (minShore c : ℝ) ≤
        ∑ e : Edge, if separates c (CertificateData.pairEndpoints e).1
          (CertificateData.pairEndpoints e).2 then q e else 0 := by
    have hadmissible : c.val.card ≠ 3 ∨ ∃ i ∈ s, balancedCut i = c := by
      by_cases hb : c.val.card = 3
      · right
        obtain ⟨i, hi⟩ := balancedCut_coverage c hb
        refine ⟨i, ?_, hi⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by simpa only [hi] using hc⟩
      · exact Or.inl hb
    have hnat := hCap c hadmissible
    have hreal : (60 : ℝ) * (minShore c : ℝ) ≤ (capacity s c : ℝ) := by
      exact_mod_cast hnat
    rw [capacity_eq]
    linarith
  calc
    (∑ c : Cut, w c * (minShore c : ℝ)) ≤
        ∑ c : Cut, w c *
          (∑ e : Edge, if separates c (CertificateData.pairEndpoints e).1
            (CertificateData.pairEndpoints e).2 then q e else 0) := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hz : w c = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hcapacity c hz) (hw c)
    _ = ∑ e : Edge, q e *
        (∑ c : Cut, if separates c (CertificateData.pairEndpoints e).1
          (CertificateData.pairEndpoints e).2 then w c else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs <;> ring
    _ ≤ ∑ e : Edge, q e := by
      apply Finset.sum_le_sum
      intro e he
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left
          (hdiam (CertificateData.pairEndpoints e).1
            (CertificateData.pairEndpoints e).2) (hq_nonneg e)
    _ ≤ 9 / 2 := hq_total

end Jung5
