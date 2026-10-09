import ErdePaths.MersenneUniformInput
import ErdePaths.MersenneGlobalFold
import ErdePaths.SourceUniformCycles

namespace ErdePaths.MersenneUniformCycles
open SquareLift MersenneAACBase

/-- The exact Mersenne odd factor, uniformly at arbitrary depth. -/
def oddPart (R : Nat) : Nat := 2^(R+1)-1
def dimension (m R : Nat) : Nat := 2*m*oddPart R
def length (m R : Nat) : Nat := oddPart R*2^(dimension m R-R-1)
def half (m R : Nat) : Nat := 2^(2*m*(2^(R-1)-1)-1)

section Construction
variable (m R : Nat) (hm : 1≤m) (hR : 4≤R)
noncomputable abbrev input := MersenneUniformInput.input m R hm hR

theorem half_pos : 0<half m R := Nat.two_pow_pos _
include hm hR in
theorem half_ge_two : 2≤half m R :=
  SourceUniformInput.j_half_ge_two m (2^(R-1)-1) hm (MersenneUniformInput.residue_odd R hR)

/-- The genuine J factors are constructed internally, not supplied. -/
noncomputable def jData : HamiltonData.DecompositionData
    (Vertex (2*m*(2^(R-1)-1))) (@Adjacent (2*m*(2^(R-1)-1)))
    ((input m R hm hR).m*(2^((input m R hm hR).k+(input m R hm hR).h)-1))
    (2*half m R) (by have := half_pos m R; omega) := by
  have hc : m*(2^(R-1)-1)=
      (input m R hm hR).m*(2^((input m R hm hR).k+(input m R hm hR).h)-1) := by
    change m*(2^(R-1)-1)=m*(2^(R-2+1)-1)
    rw [show R-2+1=R-1 by omega]
  exact EvenHamilton.castData rfl hc rfl
    (SourceUniformInput.jData m (2^(R-1)-1) hm (MersenneUniformInput.residue_odd R hR))

theorem source_count :
    (input m R hm hR).m*2^((input m R hm hR).k+(input m R hm hR).h+1)=m*2^R := by
  change m*2^(R-2+1+1)=m*2^R
  rw [show R-2+1+1=R by omega]

theorem dimension_eq :
    MersenneGlobalFold.Input.Dimension (input m R hm hR) (2*m*(2^(R-1)-1))=dimension m R :=
  MersenneUniformInput.dimension m R hm hR

theorem length_eq :
    MersenneGlobalFold.Input.totalLength (input m R hm hR) (half m R)=length m R := by
  let I := input m R hm hR
  let n : I.Index := ⟨0,by change 0<m*2^(R-2+1+1); exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)⟩
  exact (MersenneGlobalFold.Input.length_eq I (half_pos m R) n).symm.trans
    (MersenneUniformInput.length m R hm hR n)

include hm hR in
theorem length_pos : 0<length m R := by
  rw [←length_eq m R hm hR]
  exact MersenneGlobalFold.Input.totalLength_pos (input m R hm hR) (half_pos m R)

/-- Transport the actual constructed global ledger through exact index,
vertex-dimension and numeric-length equalities. No output ledger is an input. -/
private noncomputable def transport (I : MersenneAACBase.Input) {j t M N L : Nat}
    (ht : 0<t)
    (JD : HamiltonData.DecompositionData (Vertex j) (@Adjacent j)
      (I.m*(2^(I.k+I.h)-1)) (2*t) (by omega))
    (h2 : 2≤t)
    (hi : I.m*2^(I.k+I.h+1)=M)
    (hd : MersenneGlobalFold.Input.Dimension I j=N)
    (hl : MersenneGlobalFold.Input.totalLength I t=L) :
    SourceUniformCycles.CycleFamily M N L := by
  subst M
  subst N
  subst L
  have hp := MersenneGlobalFold.Input.uniform_decomposition I ht JD h2
  exact {
    positive:=MersenneGlobalFold.Input.totalLength_pos I ht
    vertex:=MersenneGlobalFold.Input.uniformTour I ht JD
    injective:=hp.1, cover:=hp.2.1, unique:=hp.2.2.1, adjacent:=hp.2.2.2 }

/-- Genuine unconditional equal-length simple Mersenne cube-cycle family.
All D/H/J factors, selectors, source origins, marks, schedules and tours are
constructed internally. Only the numeric multiplier/depth bounds are inputs. -/
noncomputable def family : SourceUniformCycles.CycleFamily (m*2^R) (dimension m R) (length m R) :=
  transport m R (input m R hm hR) (half_pos m R) (jData m R hm hR)
    (half_ge_two m R hm hR) (source_count m R hm hR)
    (dimension_eq m R hm hR) (length_eq m R hm hR)

end Construction
#print axioms jData
#print axioms dimension_eq
#print axioms length_eq
#print axioms family
end ErdePaths.MersenneUniformCycles
