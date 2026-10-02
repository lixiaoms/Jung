import Jung.ContactGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Jung

noncomputable def cutCoefficient (p : ℝ) : ℝ := 1 + (p^2 - 1) / (2*p - 1)

noncomputable def cutBound (p : ℝ) : ℝ := p^3 * (2*p - 1) / (p^3 + p - 1)

/-- The final real-algebra step of the quadratic cut estimate. -/
theorem cut_bound_of_moments (p T W Phi : ℝ) (hp : 3 ≤ p)
    (hbasic : (p+1)*Phi - p*W ≤ T)
    (hweight : p*W ≤ Phi)
    (hkey : T + cutCoefficient p * W ≤ 2*p^2) :
    Phi ≤ cutBound p := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < 2*p-1 := by linarith
  have hc : cutCoefficient p * (2*p-1) = p^2+2*p-2 := by
    unfold cutCoefficient
    rw [add_mul, div_mul_cancel₀ _ hd.ne']
    ring
  have hpc : 0 ≤ p-cutCoefficient p := by
    have hmul : 0 ≤ (p-cutCoefficient p)*(2*p-1) := by
      nlinarith [sq_nonneg (p-3)]
    exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hmul) hd
  have hm := mul_le_mul_of_nonneg_left hweight hpc
  have hPhi : (p^2+cutCoefficient p)*Phi ≤ 2*p^3 := by
    nlinarith
  have hden : 0 < p^3+p-1 := by nlinarith [pow_pos hp0 3]
  have hcoef : (p^2+cutCoefficient p)*(2*p-1) = 2*(p^3+p-1) := by
    nlinarith [hc]
  have hscaled := mul_le_mul_of_nonneg_right hPhi hd.le
  have hnum : (p^3+p-1)*Phi ≤ p^3*(2*p-1) := by
    have hscaled' : 2*(p^3+p-1)*Phi ≤ 2*p^3*(2*p-1) := by
      have heq : (p^2+cutCoefficient p)*Phi*(2*p-1) = 2*(p^3+p-1)*Phi := by
        calc
          _ = ((p^2+cutCoefficient p)*(2*p-1))*Phi := by ring
          _ = _ := by rw [hcoef]
      rwa [heq] at hscaled
    nlinarith [hscaled']
  exact (le_div_iff₀ hden).mpr (by simpa [mul_comm] using hnum)

/-- The cut bound is strictly below the contact obstruction for p at least five. -/
theorem cut_bound_strict (p : ℝ) (hp : 5 ≤ p) :
    cutBound p < 2*p*((2*p-3)/(2*p-2)) := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < p^3+p-1 := by nlinarith [pow_pos hp0 3]
  have hd : 0 < 2*p-2 := by linarith
  unfold cutBound
  rw [div_lt_iff₀ hden]
  have heq : (2*p*((2*p-3)/(2*p-2)))*(p^3+p-1)*(2*p-2) =
      2*p*(2*p-3)*(p^3+p-1) := by
    calc
      _ = (2*p*(p^3+p-1))*(((2*p-3)/(2*p-2))*(2*p-2)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hd.ne']; ring
  have hpos : 0 < p*(p^2-5*p+3) := by
    have : 0 ≤ p*(p-5) := mul_nonneg (by linarith) (by linarith)
    have : 0 < p^2-5*p+3 := by nlinarith
    exact mul_pos (by linarith) this
  have hgap : p^3*(2*p-1)*(2*p-2) <
      (2*p*((2*p-3)/(2*p-2)))*(p^3+p-1)*(2*p-2) := by
    rw [heq]
    nlinarith [hpos]
  nlinarith

end Jung
