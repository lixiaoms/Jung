import Jung.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset

namespace Jung

variable {d : ℕ}

/-- A dual sign form, kept separate from the default norm on `(Point d)`. -/
def signDot (s v : (Point d)) : ℝ := ∑ k, s k * v k

def IsSign (s : (Point d)) : Prop := ∀ k, s k = 1 ∨ s k = -1

theorem signDot_sub (s u v : (Point d)) :
    signDot s (u - v) = signDot s u - signDot s v := by
  simp only [signDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem signDot_add (s u v : (Point d)) :
    signDot s (u + v) = signDot s u + signDot s v := by
  simp only [signDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem signDot_le_l1Dist (s x y : (Point d)) (hs : IsSign s) :
    signDot s (x - y) ≤ l1Dist x y := by
  apply Finset.sum_le_sum
  intro k hk
  rcases hs k with h | h
  · simpa [h] using le_abs_self (x k - y k)
  · simpa [h] using neg_le_abs (x k - y k)

theorem weighted_signDot_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (s : ι → (Point d)) (v : (Point d))
    (hbal : ∀ k, ∑ i, w i * s i k = 0) :
    ∑ i, w i * signDot (s i) v = 0 := by
  simp only [signDot, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    intro k
    rw [show (∑ i, w i * (s i k * v k)) =
      (∑ i, w i * s i k) * v k by
        simp only [Finset.sum_mul, mul_assoc]]
    rw [hbal k, zero_mul]
  simp

/-- A selected contact can be repeated: only its own index is removed here. -/
theorem contact_weight_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p s : ι → (Point d)) (w : ι → ℝ) (c : (Point d)) (R : ℝ)
    (hs : ∀ i, IsSign (s i)) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1)
    (hbal : ∀ k, ∑ i, w i * s i k = 0)
    (hactive : ∀ i, signDot (s i) (p i - c) = R)
    (hdiam : ∀ i j, l1Dist (p i) (p j) ≤ 1) (j : ι) :
    R ≤ 1 - w j := by
  have hid : (∑ i, w i * signDot (s i) (p i - p j)) = R := by
    have hsplit (i : ι) : p i - p j = (p i - c) - (p j - c) := by
      ext k
      simp only [Pi.sub_apply]
      ring
    have hterm (i : ι) : signDot (s i) (p i - p j) =
        R - signDot (s i) (p j - c) := by
      rw [hsplit i, signDot_sub, hactive i]
    simp_rw [hterm, mul_sub]
    rw [Finset.sum_sub_distrib, weighted_signDot_zero w s (p j - c) hbal]
    rw [← Finset.sum_mul, hsum]
    ring
  have hterm (i : ι) : w i * signDot (s i) (p i - p j) ≤
      if i = j then 0 else w i := by
    by_cases hij : i = j
    · subst i
      simp [signDot]
    · simp only [hij, ↓reduceIte]
      calc
        w i * signDot (s i) (p i - p j) ≤ w i * l1Dist (p i) (p j) :=
          mul_le_mul_of_nonneg_left (signDot_le_l1Dist _ _ _ (hs i)) (hw i)
        _ ≤ w i * 1 := mul_le_mul_of_nonneg_left (hdiam i j) (hw i)
        _ = w i := mul_one _
  calc
    R = ∑ i, w i * signDot (s i) (p i - p j) := hid.symm
    _ ≤ ∑ i, if i = j then 0 else w i := Finset.sum_le_sum fun i _ => hterm i
    _ = 1 - w j := by
      have hremove : (∑ i, if i = j then 0 else w i) + w j = ∑ i, w i := by
        calc
          _ = ∑ i, ((if i = j then 0 else w i) + (if i = j then w i else 0)) := by
            rw [Finset.sum_add_distrib]
            simp
          _ = ∑ i, w i := by
            apply Finset.sum_congr rfl
            intro i hi
            split_ifs <;> simp
      linarith

/-- Balanced norming forms give a lower bound at every possible center. -/
theorem sum_contacts_lower_bound {ι : Type*} [Fintype ι]
    (p s : ι → (Point d)) (c : (Point d)) (R : ℝ)
    (hs : ∀ i, IsSign (s i))
    (hbal : ∀ k, ∑ i, s i k = 0)
    (hactive : ∀ i, signDot (s i) (p i - c) = R) (m : (Point d)) :
    (Fintype.card ι : ℝ) * R ≤ ∑ i, l1Dist (p i) m := by
  have hz : (∑ i, signDot (s i) (m - c)) = 0 := by
    simpa using weighted_signDot_zero (fun _ : ι => (1 : ℝ)) s (m - c)
      (by simpa using hbal)
  have hid : (∑ i, signDot (s i) (p i - m)) = (Fintype.card ι : ℝ) * R := by
    have hsplit (i : ι) : p i - m = (p i - c) - (m - c) := by
      ext k
      simp only [Pi.sub_apply]
      ring
    have hterm (i : ι) : signDot (s i) (p i - m) =
        R - signDot (s i) (m - c) := by
      rw [hsplit i, signDot_sub, hactive i]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, hz]
    simp
  rw [← hid]
  exact Finset.sum_le_sum fun i _ => signDot_le_l1Dist _ _ _ (hs i)

end Jung
