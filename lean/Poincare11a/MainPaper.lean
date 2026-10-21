/-
The paper's own route to Theorem 1.1: Theorem 2.2 (`reduction`) and Theorem 4.2 (`K.K_le`).
-/
import Poincare11a.MainK
import Poincare11a.Reduction

namespace Poincare11a.K

/-- Paper Theorem 2.2 (first inequality), restated in this namespace; no certificate is involved. -/
theorem reduction (n : ℕ) (f : Cube n → ℝ) :
    avg (fun x => |f x - avg f|) ≤ avg (fun y => gradNorm f y * J (fun j => D f j y / gradNorm f y)) :=
  Poincare11a.reduction n f

/-- Theorem 1.1 by the paper's route (Theorem 2.2 + Theorem 4.2). -/
theorem poincare_L1_via_reduction (n : ℕ) (f : Cube n → ℝ) :
    avg (fun x => |f x - avg f|) ≤ 71 / 50 * avg (gradNorm f) :=
  poincare_of_reduction (fun m lam h => K_le m lam h) f

end Poincare11a.K
