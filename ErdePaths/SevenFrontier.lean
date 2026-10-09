import ErdePaths.QuarterGlobalPaths
import ErdePaths.EvenHamilton

namespace ErdePaths.SevenFrontier
open SquareLift HamiltonData

/-- Genuine cube data; shifted quarter profiles and zero-depth origins are
constructed inside QuarterAACBase, with no exceptional finite certificate. -/
noncomputable def input (m : Nat) (hm : 1≤m) : QuarterAACBase.Input where
  e:=2*m
  d:=2*(m*2)
  m:=m
  B:=2^(2*(m*2))
  hB:=Nat.two_pow_pos _
  he:=by omega
  D:=EvenHamilton.decomposition m (by omega)
  HD:=EvenHamilton.decomposition (m*2) (by omega)
  last:=⟨0,Nat.two_pow_pos _⟩
  hB4:=Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 2≤2*(m*2))
  evenB:=by
    have he : 2*(m*2)=(2*(m*2)-1)+1 := by omega
    rw [he,Nat.pow_succ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)

noncomputable def jData (m : Nat) (hm : 1≤m) :
    DecompositionData (Vertex (2*m)) (@Adjacent (2*m))
      ((input m hm).m*1) (2*2^(2*m-1)) (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) := by
  have hl : 2^(2*m)=2*2^(2*m-1) := by
    calc
      2^(2*m)=2^((2*m-1)+1) := congrArg (fun q=>2^q) (by omega)
      _=2*2^(2*m-1) := by rw [Nat.pow_succ,Nat.mul_comm]
  exact EvenHamilton.castData rfl (by change m=m*1; omega) hl (EvenHamilton.decomposition m (by omega))

theorem half_ge_two (m : Nat) (hm : 1≤m) : 2≤2^(2*m-1) :=
  Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 1≤2*m-1)

theorem dimension (m : Nat) (hm : 1≤m) :
    QuarterGlobalPaths.Input.Dimension (input m hm) (2*m)=2*m*7 := by
  change 2*m*2^(1+0+1)+2*(m*2)+2*m=2*m*7
  simp only [Nat.reduceAdd,Nat.reducePow]
  omega

theorem length (m : Nat) (hm : 1≤m) :
    QuarterGlobalPaths.Input.totalLength (input m hm) (2^(2*m-1))=
      7*2^(2*m*7-2-1) := by
  have hh := UniformFoldLengths.ordinary (g:=2*m*4) (H:=2*(m*2)) (j:=2*m)
    (r:=1) (s:=1) (b:=1) (by omega) (by omega)
  change 2^(2*m-1)*(2^(2*m*2^(1+1)-1)*2^(2*(m*2))*(2+1)+
    (2^(2*m*2^(1+1)-1)/2)*2^(2*(m*2)))=_
  change 2^(2*m-1)*(2^(2*m*4-1)*2^(2*(m*2))*(2+1)+
    (2^(2*m*4-1)/2)*2^(2*(m*2)))=_
  simpa only [Nat.reduceAdd,Nat.reducePow,Nat.one_mul,
    show 2*m*4+2*(m*2)+2*m-(1+1)-1=2*m*7-2-1 by omega] using hh

/-- Actual maximal seven frontier in every even multiple of seven. -/
theorem frontier (m : Nat) (hm : 1≤m) :
    HasPathDecomposition (2*m*7) (7*2^(2*m*7-(7:Nat).log2-1)) := by
  have H := GraphTarget.to_target (QuarterGlobalPaths.Input.cube (input m hm)
    (Nat.two_pow_pos (2*m-1)) (half_ge_two m hm) (jData m hm))
  rw [dimension m hm,length m hm] at H
  simpa only [show (7:Nat).log2=2 by decide] using H

#print axioms frontier
end ErdePaths.SevenFrontier
