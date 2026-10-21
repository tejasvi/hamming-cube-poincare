/- Track N: the certificate computations, closed by `native_decide`. -/
import Poincare11a.Data.Lib
import Poincare11a.Data.Ivl
import Poincare11a.Data.Leaves

namespace Poincare11a.CertN
open Poincare11a.Cert Poincare11a.Data

theorem lib_allPos : lib.allPos = true := by native_decide
theorem ivs_partOK : partOK ivs = true := by native_decide
theorem tree_check : tree.check lib ivs 0 0 0 = true := by native_decide

end Poincare11a.CertN
