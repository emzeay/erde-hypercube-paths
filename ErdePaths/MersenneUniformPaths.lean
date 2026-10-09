import ErdePaths.MersenneGlobalPaths
import ErdePaths.MersenneUniformCycles
import ErdePaths.OddClassification

namespace ErdePaths.MersenneUniformPaths

/-- Actual simple paths at every complementary binary frontier of depth at
least four. Source/H/J factors, selectors, schedules, isolated neighbors,
forks and complete binary-cube edge ownership are constructed internally. -/
theorem decomposition (m R : Nat) (hm : 1≤m) (hR : 4≤R) :
    HasPathDecomposition (2*m*(2^(R+1)-1))
      ((2^(R+1)-1)*2^(2*m*(2^(R+1)-1)-R-1)) := by
  have H := GraphTarget.to_target (MersenneGlobalPaths.Input.cube
    (MersenneUniformCycles.input m R hm hR)
    (MersenneUniformCycles.half_pos m R)
    (MersenneUniformCycles.half_ge_two m R hm hR)
    (MersenneUniformCycles.jData m R hm hR))
  rw [MersenneUniformCycles.dimension_eq m R hm hR,
    MersenneUniformCycles.length_eq m R hm hR] at H
  exact H

/-- The same actual path partition in canonical odd-frontier notation. -/
theorem frontier (m R : Nat) (hm : 1≤m) (hR : 4≤R) :
    let d := 2^(R+1)-1
    HasPathDecomposition (2*m*d) (d*2^(2*m*d-d.log2-1)) := by
  dsimp only
  rw [OddClassification.mersenne_log2 (show 1≤R by omega)]
  exact decomposition m R hm hR

#print axioms decomposition
#print axioms frontier
end ErdePaths.MersenneUniformPaths
