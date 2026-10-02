import Jung5.ContactAlgebra

open scoped BigOperators

namespace Jung5

/-- Six balanced sign vectors with every weight below a quarter are also
balanced with uniform weights. The 64 sign patterns in one coordinate are
checked by ordinary exact linear arithmetic in the kernel. -/
theorem six_uniform_balance (s : Fin 6 → Point) (w : Fin 6 → ℝ)
    (hs : ∀ i, IsSign (s i))
    (hsum : ∑ i, w i = 1)
    (hbal : ∀ k, ∑ i, w i * s i k = 0)
    (hw : ∀ i, w i < (1 : ℝ) / 4) :
    ∀ k, ∑ i, s i k = 0 := by
  have hw0 := hw 0
  have hw1 := hw 1
  have hw2 := hw 2
  have hw3 := hw 3
  have hw4 := hw 4
  have hw5 := hw 5
  norm_num [Fin.sum_univ_succ] at hsum
  intro k
  have hb := hbal k
  rcases hs 0 k with h0 | h0 <;>
    rcases hs 1 k with h1 | h1 <;>
    rcases hs 2 k with h2 | h2 <;>
    rcases hs 3 k with h3 | h3 <;>
    rcases hs 4 k with h4 | h4 <;>
    rcases hs 5 k with h5 | h5
  all_goals norm_num [Fin.sum_univ_succ, h0, h1, h2, h3, h4, h5] at hb ⊢
  all_goals linarith

/-- Once a six-member balanced contact family exists, radius above three
quarters forces the strict sum-distance obstruction at every center. -/
theorem six_contact_obstruction (p s : Fin 6 → Point) (w : Fin 6 → ℝ)
    (c : Point) (R : ℝ)
    (hs : ∀ i, IsSign (s i)) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1)
    (hbal : ∀ k, ∑ i, w i * s i k = 0)
    (hactive : ∀ i, signDot (s i) (p i - c) = R)
    (hdiam : ∀ i j, l1Dist (p i) (p j) ≤ 1)
    (hR : (3 : ℝ) / 4 < R) :
    ∀ m : Point, (9 : ℝ) / 2 < ∑ i, l1Dist (p i) m := by
  have hsmall (i : Fin 6) : w i < (1 : ℝ) / 4 := by
    have hle := contact_weight_bound p s w c R hs hw hsum hbal hactive hdiam i
    linarith
  have hu := six_uniform_balance s w hs hsum hbal hsmall
  intro m
  have hle := sum_contacts_lower_bound p s c R hs hu hactive m
  norm_num at hle
  linarith

end Jung5
