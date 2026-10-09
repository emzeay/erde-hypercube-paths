import ErdePaths.SourceUniformInput
import ErdePaths.SourceGlobalFold

namespace ErdePaths.SourceUniformCycles
open SquareLift HamiltonData

/-- Two simple cyclic tours per index, with literal cyclic successor and
exact once ownership of every undirected edge of the binary cube. -/
structure CycleFamily (M N L : Nat) where
  positive : 0<L
  vertex : Fin M → Bool → Fin L → Vertex N
  injective : ∀i c, Function.Injective (vertex i c)
  cover : ∀x y : Vertex N, Adjacent x y → ∃i c p,
    SameEdge (vertex i c p,vertex i c (successor positive p)) (x,y)
  unique : ∀i c p i' c' p',
    SameEdge (vertex i c p,vertex i c (successor positive p))
      (vertex i' c' p',vertex i' c' (successor positive p')) →
    i=i' ∧ c=c' ∧ p=p'
  adjacent : ∀i c p, Adjacent (vertex i c p) (vertex i c (successor positive p))

private noncomputable def transport (I : SourceLocalFold.Input) {j t M N L : Nat}
    (ht : 0<t)
    (JD : DecompositionData (Vertex j) (@Adjacent j) (I.m*I.b) (2*t) (by omega))
    (h2 : 2≤t)
    (hi : I.m*2^(I.a+I.h+1)=M)
    (hd : SourceGlobalFold.Input.Dimension I j=N)
    (hl : SourceGlobalFold.Input.totalLength I t=L) : CycleFamily M N L := by
  subst M
  subst N
  subst L
  have hp := SourceGlobalFold.Input.uniform_decomposition I ht JD h2
  exact {
    positive:=SourceGlobalFold.Input.totalLength_pos I ht
    vertex:=SourceGlobalFold.Input.uniformTour I ht JD
    injective:=hp.1, cover:=hp.2.1, unique:=hp.2.2.1, adjacent:=hp.2.2.2 }

/-- Actual ordinary-frontier cycle partition. Every input factor, profile,
mark schedule, return matching and binary-coordinate transport is constructed
internally; the only premises are these numerical parameter restrictions.
This is a cyclic decomposition; opening the tours into paths is separate. -/
noncomputable def family (m R r b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hr : 1≤r) (hrR : r<R) (hb : b<2^(R-r)) (ho : b%2=1) :
    CycleFamily (m*2^R) (2*m*(2^R+2^(R-r)+b))
      ((2^R+2^(R-r)+b)*2^(2*m*(2^R+2^(R-r)+b)-R-1)) := by
  let I := SourceUniformInput.input m R r b hm hR hr hrR hb ho
  let t := 2^(2*m*b-1)
  have ht : 0<t := Nat.two_pow_pos _
  have h2 : 2≤t := SourceUniformInput.j_half_ge_two m b hm ho
  have hi : I.m*2^(I.a+I.h+1)=m*2^R := by
    change m*2^(R-2+1+1)=m*2^R
    rw [show R-2+1+1=R by omega]
  have hn : 0<I.m*2^(I.a+I.h+1) := by
    change 0<m*2^(R-2+1+1)
    exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  let n : I.Index := ⟨0,hn⟩
  have hl := SourceUniformInput.length m R r b hm hR hr hrR hb ho n
  have hl' := SourceGlobalFold.Input.length_eq I ht n
  have he : SourceGlobalFold.Input.totalLength I t=
      (2^R+2^(R-r)+b)*2^(2*m*(2^R+2^(R-r)+b)-R-1) := hl'.symm.trans hl
  exact transport I ht (SourceUniformInput.jData m b hm ho) h2 hi
    (SourceUniformInput.dimension m R r b hm hR hr hrR hb ho) he

#print axioms family
end ErdePaths.SourceUniformCycles
