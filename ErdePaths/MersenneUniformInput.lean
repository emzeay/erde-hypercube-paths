import ErdePaths.MersenneAACBase
import ErdePaths.SourceUniformInput

namespace ErdePaths.MersenneUniformInput
open SourceClock SourceProfile MersenneAACBase

/-- The actual small/large incidence branch is determined by dimension. -/
def branch (m R : Nat) (hm : 1≤m) (hR : 4≤R) : Branch (2*m) (R-2) := by
  by_cases he : m=1
  · have hk : R-2=(R-4)+2 := by omega
    rw [he,hk]
    exact Branch.small (R-4)
  · exact Branch.large (by omega) (by omega)

/-- Genuine source data for arbitrary Mersenne depth and even multiplier,
with the complementary long word and its actual exceptional flag. -/
noncomputable def input (m R : Nat) (hm : 1≤m) (hR : 4≤R) : Input := by
  have he : 2≤2*m := by omega
  have hsum : R-2+1+1=R := by omega
  have hsum' : R-2+1+3=R+2 := by omega
  have hroom : R+2≤2*m*2^(R-2) := SourceRoom.mersenne_prefix_room hm hR
  have hpr : 2^1<2^(2*m*2^(R-2)) :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr (by omega)
  have hf : m*(2*2^(R-2+1-1))=m*2^(R-1) := by
    rw [Nat.mul_comm 2,←Nat.pow_succ]
    congr 2
    omega
  refine {
    e:=2*m, d:=2*(m*2^(R-1)), m:=m
    B:=2^(2*(m*2^(R-1))), k:=R-2, h:=1
    branch:=branch m R hm hR
    hB:=Nat.two_pow_pos _, hh:=by decide
    room:=?_
    D:=EvenHamilton.decomposition m (by omega)
    S:=fun _ _=>SourceUniformInput.selector 1
    ho:=fun _ _=>SourceUniformInput.selector_odd (by decide) hpr
    balance:=fun _ _=>SourceUniformInput.selector_prefix (by decide) hpr
    HD:=?_, last:=⟨0,Nat.two_pow_pos _⟩
    z:=⟨1,by decide⟩, hz:=by decide
    hB4:=?_, evenB:=?_ }
  · rw [lengthPower_pow,hsum']
    exact Nat.pow_dvd_pow 2 hroom
  · exact EvenHamilton.castData rfl hf.symm rfl
      (EvenHamilton.decomposition (m*2^(R-1)) (Nat.mul_pos (by omega) (Nat.two_pow_pos _)))
  · have hm' : 1≤m*2^(R-1) := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    exact Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 2≤2*(m*2^(R-1)))
  · have hp : 2*(m*2^(R-1))=(2*(m*2^(R-1))-1)+1 := by
      have := Nat.mul_pos (by omega : 0<m) (Nat.two_pow_pos (R-1)); omega
    rw [hp,Nat.pow_succ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)

/-- Complementary residue is positive odd at every allowed depth. -/
theorem residue_odd (R : Nat) (hR : 4≤R) : (2^(R-1)-1)%2=1 := by
  have he : R-1=(R-2)+1 := by omega
  have hp : 2^(R-1)%2=0 := by
    rw [he,Nat.pow_succ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)
  have := Nat.two_pow_pos (R-1)
  omega

/-- Exact literal target dimension, with no ambient isomorphism premise. -/
theorem dimension (m R : Nat) (hm : 1≤m) (hR : 4≤R) :
    let I := input m R hm hR
    I.e*2^(I.k+I.h+1)+I.d+2*m*(2^(R-1)-1)=2*m*(2^(R+1)-1) := by
  change 2*m*2^(R-2+1+1)+2*(m*2^(R-1))+2*m*(2^(R-1)-1)=_
  rw [show R-2+1+1=R by omega]
  have hp : 2^R=2*2^(R-1) := by
    rw [Nat.mul_comm,←Nat.pow_succ]; congr 1; omega
  have hb : 2^R+2^(R-1)+(2^(R-1)-1)=2^(R+1)-1 := by
    rw [Nat.pow_succ,hp]
    have := Nat.two_pow_pos (R-1)
    omega
  calc
    _=2*m*(2^R+2^(R-1)+(2^(R-1)-1)) := by rw [Nat.mul_add,Nat.mul_add]; ac_rfl
    _=_ := by rw [hb]

/-- Exact actual folded Mersenne frontier length at every allowed depth. -/
theorem length (m R : Nat) (hm : 1≤m) (hR : 4≤R)
    (n : (input m R hm hR).Index) :
    let I := input m R hm hR
    I.length (jR:=2^(2*m*(2^(R-1)-1)-1)) n=
      (2^(R+1)-1)*2^(2*m*(2^(R+1)-1)-R-1) := by
  let I := input m R hm hR
  have ho := residue_odd R hR
  have hp : 1≤2*m*(2^(R-1)-1) := by
    have hb : 1≤2^(R-1)-1 := by omega
    have hp := Nat.mul_le_mul hm hb
    rw [Nat.mul_assoc]
    omega
  have hh := I.frontier_length n (2*(m*2^(R-1))) (2*m*(2^(R-1)-1)) hp rfl
  change I.length (jR:=2^(2*m*(2^(R-1)-1)-1)) n=_
  change I.length (jR:=2^(2*m*(2^(R-1)-1)-1)) n=
    (2^(R-2+1+2)-1)*
      2^(2*m*2^(R-2+1+1)+2*(m*2^(R-1))+2*m*(2^(R-1)-1)-(R-2+1+1)-1) at hh
  have he := dimension m R hm hR
  change 2*m*2^(R-2+1+1)+2*(m*2^(R-1))+2*m*(2^(R-1)-1)=_ at he
  rw [he,show R-2+1+1=R by omega,show R-2+1+2=R+1 by omega] at hh
  exact hh

#print axioms branch
#print axioms input
#print axioms dimension
#print axioms length
end ErdePaths.MersenneUniformInput
