import ErdePaths.EvenHamilton
import ErdePaths.HamiltonCut

namespace ErdePaths.PowerFrontier

/-- Actual odd-part-one frontier for every positive even dimension. -/
theorem frontier (m : Nat) (hm : 1≤m) :
    HasPathDecomposition (2*m) (2^(2*m-1)) := by
  have hn : 1≤2*m := by omega
  have he : 2*m-1<2*m := by omega
  exact HamiltonCut.cube_cut (EvenHamilton.decomposition m (by omega))
    (Nat.two_pow_pos _) ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr he)
    (Nat.pow_dvd_pow 2 (by omega))

#print axioms frontier
end ErdePaths.PowerFrontier
