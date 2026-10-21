/-
Track N: Theorem 1.1 (C_11a ≤ 71/50) with the certificate computations closed by `native_decide`.
-/
import Poincare11a.KLe
import Poincare11a.Constant
import Poincare11a.CertN

namespace Poincare11a.N

open Poincare11a Poincare11a.Cert Poincare11a.Data

/-- Paper Theorem 1.1: `E|f - Ef| ≤ (71/50) E|∇f|` for every `n` and every `f : {-1,1}^n → ℝ`. -/
theorem poincare_L1 (n : ℕ) (f : Cube n → ℝ) :
    avg (fun x => |f x - avg f|) ≤ 71 / 50 * avg (gradNorm f) :=
  poincare_of_cert lib CertN.lib_allPos ivs CertN.ivs_partOK tree
    (QT.OK_of_check lib ivs tree 0 0 0 CertN.tree_check) f

/-- Paper Theorem 1.1 in the form `C ≤ 71/50`. -/
theorem C11a_le : C11a ≤ 71 / 50 := C11a_le_of_valid poincare_L1

/-- The trivial lower bound, which makes the infimum `C11a` meaningful. -/
theorem one_le_C11a : 1 ≤ C11a := one_le_C11a_of_valid poincare_L1

/-- Paper Theorem 4.2: `K ≤ 71/50`, i.e. `J(λ) ≤ 71/50` for every unit vector in every dimension. -/
theorem K_le (n : ℕ) (lam : Fin n → ℝ) (h : ∑ j, lam j ^ 2 = 1) : J lam ≤ 71 / 50 :=
  K_le_of_cert lib CertN.lib_allPos ivs CertN.ivs_partOK tree
    (QT.OK_of_check lib ivs tree 0 0 0 CertN.tree_check) lam h

end Poincare11a.N
