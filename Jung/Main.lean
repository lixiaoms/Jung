import Jung.Finite
import Jung5.Main

open scoped BigOperators

namespace Jung

/-- The upper bound for every k at least one, including the independently
rebuilt five-dimensional proof. The center is unrestricted in the ambient space. -/
theorem jung_l1_four_k_plus_one_all (k : ℕ) (hk : 1 ≤ k)
    (X : Set (Point (4*k+1))) (hne : X.Nonempty) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ x∈X,∀ y∈X,l1Dist x y ≤ D) :
    ∃ c : Point (4*k+1),∀ x∈X,l1Dist x c ≤ coefficient k*D := by
  by_cases hk1 : k=1
  · subst k
    have hfive := Jung5.jung_l1_five X hne D hD hdiam
    convert hfive using 1 <;> norm_num [coefficient,l1Dist,Jung5.l1Dist] <;> ring
  · exact jung_l1_four_k_plus_one k (by omega) X hne D hD hdiam

/-- The entire original real l1 statement, with no finite, contact, sorting,
cut, or boundedness hypothesis beyond the stated pairwise bound. -/
theorem jung_l1_four_k_plus_one_explicit (k : ℕ) (hk : 1 ≤ k)
    (X : Set (Fin (4*k+1) → ℝ)) (hne : X.Nonempty) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ x∈X,∀ y∈X,(∑ j : Fin (4*k+1),|x j-y j|) ≤ D) :
    ∃ c : Fin (4*k+1) → ℝ,∀ x∈X,
      (∑ j : Fin (4*k+1),|x j-c j|) ≤ ((4*(k:ℝ)-1)/(4*(k:ℝ)))*D :=
  jung_l1_four_k_plus_one_all k hk X hne D hD hdiam

end Jung
