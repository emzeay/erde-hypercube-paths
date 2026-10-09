import ErdePaths.ZeroUpperGlobalPaths
import ErdePaths.EvenHamilton
import ErdePaths.SourceUniformInput
import ErdePaths.OddClassification

namespace ErdePaths.FifteenFrontier
open SquareLift SourceClock SourceProfile ZeroUpperAACBase

/-- The actual incidence regime is determined by the genuine parent dimension. -/
def branch (m : Nat) (hm : 1≤m) : Branch (2*m) 2 := by
  by_cases he : m=1
  · rw [he]; exact Branch.small 0
  · exact Branch.large (by omega) (by decide)

/-- Actual zero-upper singleton-profile input at arbitrary multiplier. All
parent and H factors are constructed by the uniform even-cube theorem. -/
noncomputable def input (m : Nat) (hm : 1≤m) : Input := by
  have he : 2≤2*m := by omega
  have hf : 4*m=m*(2*2^(2+0-1)) := by omega
  refine {
    e:=2*m, d:=2*(4*m), m:=m, B:=2^(2*(4*m)), k:=2
    branch:=branch m hm, hB:=Nat.two_pow_pos _, room:=?_
    D:=EvenHamilton.decomposition m (by omega)
    HD:=?_, last:=⟨0,Nat.two_pow_pos _⟩
    z:=⟨1,by decide⟩, hz:=by decide, hB4:=?_, evenB:=?_ }
  · rw [lengthPower_pow]
    exact Nat.pow_dvd_pow 2 (by omega : 2+0+3≤2*m*2^2)
  · exact EvenHamilton.castData rfl hf rfl
      (EvenHamilton.decomposition (4*m) (by omega))
  · exact Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 2≤2*(4*m))
  · have hp : 2*(4*m)=(2*(4*m)-1)+1 := by omega
    rw [hp,Nat.pow_succ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)

def half (m : Nat) := 2^(2*m*3-1)
theorem half_pos (m : Nat) : 0<half m := Nat.two_pow_pos _
theorem half_ge_two (m : Nat) (hm : 1≤m) : 2≤half m := by
  exact Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 1≤2*m*3-1)

/-- The actual three-m-factor J family, constructed internally. -/
noncomputable def jData (m : Nat) (hm : 1≤m) :
    HamiltonData.DecompositionData (Vertex (2*m*3)) (@Adjacent (2*m*3))
      ((input m hm).m*(2^((input m hm).k+0)-1))
      (2*half m) (by have := half_pos m; omega) := by
  change HamiltonData.DecompositionData (Vertex (2*m*3)) (@Adjacent (2*m*3))
    (m*(2^2-1)) (2*half m) _
  have hn : 2*m*3=2*(m*3) := by omega
  have hL : 2^(2*(m*3))=2*half m := by
    unfold half
    rw [show 2*(m*3)=(2*m*3-1)+1 by omega,Nat.pow_succ]
    omega
  exact EvenHamilton.castData hn.symm (by rfl : m*3=m*(2^2-1)) hL
    (EvenHamilton.decomposition (m*3) (by omega))

theorem dimension_eq (m : Nat) (hm : 1≤m) :
    ZeroUpperGlobalPaths.Fold.Input.Dimension (input m hm) (2*m*3)=2*m*15 := by
  change 2*m*2^(2+0+1)+2*(4*m)+2*m*3=2*m*15
  omega

/-- Exact frontier length from the genuine long-word folded cardinality. -/
theorem length_eq (m : Nat) (hm : 1≤m) :
    ZeroUpperGlobalPaths.Fold.Input.totalLength (input m hm) (half m)=
      15*2^(2*m*15-4) := by
  have hh:=UniformFoldLengths.mersenne
    (g:=2*m*2^3) (H:=2*(4*m)) (j:=2*m*3) (R:=3)
    (by omega : 3+2≤2*m*2^3) (by decide) (by omega : 1≤2*m*3)
  change 2^(2*m*3-1)*(2^(2*m*2^(2+0+1)-1)*2^(2*(4*m))*3+
    (2*2^(2+0+1)-4)*(2^(2*m*2^(2+0+1)-1)/(2*2^(2+0+1)))*2^(2*(4*m)))=_
  rw [hh]
  congr 1
  congr 1
  omega

/-- For every multiplier, the full Q_(30m) edge set partitions into actual
simple paths of length 15*2^(30m-4). No factor, profile, balance, mark-count,
cover, geometry, fork or output existence input remains. -/
theorem decomposition (m : Nat) (hm : 1≤m) :
    HasPathDecomposition (2*m*15) (15*2^(2*m*15-4)) := by
  have H:=GraphTarget.to_target (ZeroUpperGlobalPaths.Input.cube
    (input m hm) (half_pos m) (half_ge_two m hm) (jData m hm))
  rw [dimension_eq m hm,length_eq m hm] at H
  exact H

theorem frontier (m : Nat) (hm : 1≤m) :
    HasPathDecomposition (2*m*15) (15*2^(2*m*15-(15).log2-1)) := by
  change HasPathDecomposition (2*m*15) (15*2^(2*m*15-3-1))
  rw [Nat.sub_sub]
  exact decomposition m hm

#print axioms input
#print axioms jData
#print axioms length_eq
#print axioms decomposition
#print axioms frontier
end ErdePaths.FifteenFrontier
