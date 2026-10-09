import ErdePaths.HamiltonOrient
import ErdePaths.SourceRoom
import ErdePaths.EvenHamilton
import ErdePaths.AnchoredAssembly
import ErdePaths.SourceAnchorCoordinates
import ErdePaths.GraphTarget

namespace ErdePaths.TwoBitFrontier
open SourceClock HamiltonTower HamiltonData SquareLift HierarchicalDecode

/-- All R low clock bits, without the reserved profile bit of the AAC route. -/
noncomputable def addressCode {R : Nat} (address : Address R) : Vertex R :=
  Classical.choose (binaryTuple_surjective address)

theorem addressCode_bits {R : Nat} (address : Address R) :
    binaryTuple (addressCode address)=address :=
  Classical.choose_spec (binaryTuple_surjective address)

/-- Numeric phase equality is exactly the full fixed low-bit address. -/
theorem phase_iff {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N)
    (R : Nat) (v : VertexPower V R) (address : Address R) :
    ((iteratedClock hN C R address).position v).val%2^R=(addressCode address).val ↔
      address=sourceBits hN C R v address := by
  let x : Vertex R := ⟨((iteratedClock hN C R address).position v).val%2^R,
    Nat.mod_lt _ (Nat.two_pow_pos R)⟩
  have hx : binaryTuple x=sourceBits hN C R v address := by
    funext i
    simp only [binaryTuple,x,sourceBits,Nat.testBit_mod_two_pow,
      show (decide (i.val<R))=true from by simp,Bool.true_and]
  constructor
  · intro he
    have hh : x=addressCode address := Fin.ext he
    have hb := congrArg binaryTuple hh
    rw [hx,addressCode_bits] at hb
    exact hb.symm
  · intro he
    have hh : x=addressCode address := binaryTuple_injective (hx.trans (he.symm.trans (addressCode_bits address).symm))
    exact congrArg Fin.val hh

/-- Unique actual spaced phase owner follows from diagonal clocks, with
strict prefix causality derived internally. -/
theorem unique_phase {V : Type} {N : Nat} (hN : 0<N) (hEven : 2∣N)
    (C : ClockData V N) (R : Nat) (v : VertexPower V R) :
    ∃address : Address R,
      ((iteratedClock hN C R address).position v).val%2^R=(addressCode address).val ∧
      ∀address', ((iteratedClock hN C R address').position v).val%2^R=(addressCode address').val →
        address'=address := by
  obtain ⟨address,he,hu⟩ := unique_source_address hN hEven C R v
  exact ⟨address,(phase_iff hN C R v address).mpr he,
    fun address' hh=>hu address' ((phase_iff hN C R v address').mp hh)⟩

noncomputable def parent {m : Nat} (R : Nat) (i : Fin (count m R)) : Fin m :=
  Classical.choose (code_surjective R i)

noncomputable def address {m : Nat} (R : Nat) (i : Fin (count m R)) : Address R :=
  Classical.choose (Classical.choose_spec (code_surjective R i))

theorem code_coordinates {m : Nat} (R : Nat) (i : Fin (count m R)) :
    code R (parent R i) (address R i)=i :=
  Classical.choose_spec (Classical.choose_spec (code_surjective R i))

theorem coordinates_code {m : Nat} (R : Nat) (f : Fin m) (a : Address R) :
    parent R (code R f a)=f ∧ address R (code R f a)=a :=
  code_injective R _ _ _ _ (code_coordinates R (code R f a))

section Factors
variable {V : Type} {R₀ : V→V→Prop} {m N : Nat} {hN : 0<N}
variable (D : DecompositionData V R₀ m N hN) (h4 : 4≤N) (k : Nat)

noncomputable def start (room : 2^k≤lengthPower N k) (i : Fin (count m k)) :
    Fin (lengthPower N k) :=
  ⟨(addressCode (address k i)).val, Nat.lt_of_lt_of_le (addressCode (address k i)).isLt room⟩

/-- Literal rotated standard-square factors retain the entire genuine edge
partition, while their starts encode each factor's actual source address. -/
noncomputable def factors (room : 2^k≤lengthPower N k) :
    DecompositionData (VertexPower V k) (relation R₀ k) (count m k)
      (lengthPower N k) (lengthPower_positive hN k) :=
  HamiltonOrient.factors (decomposition D h4 k) (start (m:=m) k room) (fun _=>true)

/-- Actual inverse position modulo the representative spacing, with the
literal rotation start preserved. -/
theorem position_zero_iff (room : 2^k≤lengthPower N k) (hd : 2^k∣lengthPower N k)
    (i : Fin (count m k)) (v : VertexPower V k) :
    (((factors D h4 k room).cycles i).position v).val%2^k=0 ↔
    ((iteratedClock hN (D.cycles (parent k i)).toClockData k (address k i)).position v).val%2^k=
      (addressCode (address k i)).val := by
  have hh := SourceAnchorCoordinates.grid_residue_iff (lengthPower_positive hN k)
    (Nat.two_pow_pos k) hd ((decomposition D h4 k).cycles i).toClockData
    (start (m:=m) k room i) ⟨0,lengthPower_positive hN k⟩ true v
  have hc : ((decomposition D h4 k).cycles i).toClockData=
      iteratedClock hN (D.cycles (parent k i)).toClockData k (address k i) := by
    have hh := clock_eq D h4 k (parent k i) (address k i)
    rw [code_coordinates k i] at hh
    exact hh
  simp only [OrientedClock.index,Bool.not_true,Bool.false_eq_true,ite_false,
    backward_zero,SourceStability.signedOffset,ite_true,
    Nat.one_mul,shiftedResidue,Nat.zero_mod,Nat.sub_zero,Nat.add_mod_right,
    Nat.mod_eq_of_lt (addressCode (address k i)).isLt,start] at hh
  change (((factors D h4 k room).cycles i).position v).val%2^k=0 ↔ _ at hh
  rw [hc] at hh
  exact hh

/-- Every physical vertex has exactly one actual rotated representative
factor above each initial Hamilton parent. -/
theorem representative_owner (hEven : 2∣N) (room : 2^k≤lengthPower N k)
    (hd : 2^k∣lengthPower N k) (f : Fin m) (v : VertexPower V k) :
    ∃i : Fin (count m k), parent k i=f ∧
      (((factors D h4 k room).cycles i).position v).val%2^k=0 ∧
      ∀j, parent k j=f → (((factors D h4 k room).cycles j).position v).val%2^k=0 → j=i := by
  obtain ⟨a,ha,hu⟩ := unique_phase hN hEven (D.cycles f).toClockData k v
  let i := code k f a
  have hc := coordinates_code k f a
  have hi : (((factors D h4 k room).cycles i).position v).val%2^k=0 := by
    apply (position_zero_iff D h4 k room hd i v).mpr
    simpa only [i,hc.1,hc.2] using ha
  refine ⟨i,hc.1,hi,?_⟩
  intro j hj hz
  have he := (position_zero_iff D h4 k room hd j v).mp hz
  rw [hj] at he
  have ha' := hu (address k j) he
  rw [←code_coordinates k j,hj,ha']

/-- Generic length transport does not alter any actual factor or position. -/
private def lengthCast {X : Type} {T : X→X→Prop} {u L M : Nat} {hL : 0<L} {hM : 0<M}
    (he : L=M) (D : DecompositionData X T u L hL) : DecompositionData X T u M hM := by
  subst M
  exact D

private theorem lengthCast_position {X : Type} {T : X→X→Prop} {u L M : Nat} {hL : 0<L} {hM : 0<M}
    (he : L=M) (D : DecompositionData X T u L hL) (i : Fin u) (v : X) :
    ((lengthCast (hM:=hM) he D).cycles i).position v=Fin.cast he ((D.cycles i).position v) := by
  subst M
  rfl

/-- Explicit anchored factor data, with representative ownership DERIVED
from actual standard-square clocks; no representative or host-cover premise. -/
noncomputable def factorData {W : Type} {S : W→W→Prop} {B a : Nat} {hB : 0<B}
    (H : DecompositionData W S m B hB) (ha : 0<a) (hEven : 2∣N)
    (room : 2^k≤lengthPower N k) (hd : 2^k∣lengthPower N k)
    (hlen : lengthPower N k=(2*a)*2^k) :
    AnchoredAssembly.FactorData (VertexPower V k) W (relation R₀ k) S
      a B (2^k) (count m k) m ha hB (Nat.two_pow_pos k) := by
  let F := factors D h4 k room
  let E := lengthCast (hM:=Nat.mul_pos (show 0<2*a by omega) (Nat.two_pow_pos k)) hlen F
  have hz (i : Fin (count m k)) (v : VertexPower V k) :
      ((E.cycles i).position v).val%2^k=((F.cycles i).position v).val%2^k := by
    rw [lengthCast_position]
    rfl
  refine {
    G:=fun i=>(E.cycles i).cycle
    H:=fun j=>(H.cycles j).cycle
    association:=parent k
    G_injective:=fun i=>cycle_injective (E.cycles i)
    H_injective:=fun j=>cycle_injective (H.cycles j)
    G_surjective:=fun i=>cycle_surjective (E.cycles i)
    H_surjective:=fun j=>cycle_surjective (H.cycles j)
    R_symm:=E.symmetric, S_symm:=H.symmetric
    R_loopfree:=E.loopfree, S_loopfree:=H.loopfree
    G_adjacent:=fun i=>(E.cycles i).adjacent
    H_adjacent:=fun j=>(H.cycles j).adjacent
    G_cover:=E.cover, H_cover:=H.cover
    G_unique:=E.unique, H_unique:=H.unique
    representative_cover:=?_, representative_unique:=?_ }
  · intro f v
    obtain ⟨i,hf,hi,_⟩ := representative_owner D h4 k hEven room hd f v
    have hi' : ((E.cycles i).position v).val%2^k=0 := by rw [hz]; exact hi
    obtain ⟨z,hz'⟩ := (SourceAnchorCoordinates.anchor_vertices_iff (Nat.two_pow_pos k)
      (E.cycles i).toClockData v).mpr hi'
    exact ⟨i,z,hf,hz'⟩
  · intro i z j w hp he
    let v := (E.cycles i).cycle (AnchoredEmbedding.positionEncode z ⟨0,Nat.two_pow_pos k⟩)
    have hi : ((F.cycles i).position v).val%2^k=0 := by
      rw [←hz]
      apply (SourceAnchorCoordinates.anchor_vertices_iff (Nat.two_pow_pos k) (E.cycles i).toClockData v).mp
      exact ⟨z,rfl⟩
    have hj : ((F.cycles j).position v).val%2^k=0 := by
      rw [←hz]
      apply (SourceAnchorCoordinates.anchor_vertices_iff (Nat.two_pow_pos k) (E.cycles j).toClockData v).mp
      exact ⟨w,he.symm⟩
    obtain ⟨owner,_,_,hu⟩ := representative_owner D h4 k hEven room hd (parent k i) v
    have hij : i=j := (hu i rfl hi).trans (hu j hp.symm hj).symm
    subst j
    have hh := cycle_injective (E.cycles i) he
    have hd' := congrArg (AnchoredEmbedding.positionDecode (Nat.two_pow_pos k)) hh
    simp only [AnchoredEmbedding.positionDecode_encode] at hd'
    exact ⟨rfl,congrArg Prod.fst hd'⟩

end Factors
/-- Room for a nondegenerate coarse torus, uniformly including R=1. -/
theorem exponent_room {m R : Nat} (hm : 1≤m) (hR : 1≤R) :
    R+2≤2*m*2^R := by
  have hh := SourceRoom.non_mersenne_bound (R-1)
  rw [show R-1+1=R by omega,show R-1+3=R+2 by omega] at hh
  have hm' := Nat.mul_le_mul_right (2^R) (show 2≤2*m by omega)
  omega

abbrev gridHalf (m R : Nat) := 2^(2*m*2^R-R-1)
abbrev Base (m R : Nat) := VertexPower (Vertex (2*m)) R
abbrev BaseRelation (m R : Nat) := relation (@Adjacent (2*m)) R

/-- Entire representative/factor input to the anchored torus theorem,
constructed for every two-bit coefficient from actual even-cube factors. -/
noncomputable def actualData (m R : Nat) (hm : 1≤m) (hR : 1≤R) :
    AnchoredAssembly.FactorData (Base m R) (Vertex (2*m)) (BaseRelation m R) (@Adjacent (2*m))
      (gridHalf m R) (2^(2*m)) (2^R) (count m R) m
      (Nat.two_pow_pos _) (Nat.two_pow_pos _) (Nat.two_pow_pos _) := by
  let D := EvenHamilton.decomposition m (by omega)
  have h4 : 4≤2^(2*m) := Nat.pow_le_pow_right (show 1≤2 by decide) (show 2≤2*m by omega)
  have hex := exponent_room hm hR
  have hl : lengthPower (2^(2*m)) R=(2*gridHalf m R)*2^R := by
    rw [SourceProfile.lengthPower_pow]
    change 2^(2*m*2^R)=(2*2^(2*m*2^R-R-1))*2^R
    rw [Nat.mul_comm 2 (2^(2*m*2^R-R-1)),←Nat.pow_succ,←Nat.pow_add]
    congr 1
    omega
  have hd : 2^R∣lengthPower (2^(2*m)) R := by
    rw [SourceProfile.lengthPower_pow]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hroom : 2^R≤lengthPower (2^(2*m)) R := by
    rw [SourceProfile.lengthPower_pow]
    exact Nat.pow_le_pow_right (by decide : 1≤2) (by omega)
  have hev : 2∣2^(2*m) := by
    have he : 2*m=(2*m-1)+1 := by omega
    rw [he,Nat.pow_succ]
    exact Nat.dvd_mul_left 2 _
  exact factorData D h4 R D (Nat.two_pow_pos _) hev hroom hd hl

/-- Explicit appended binary coordinates for the actual tower times base
cube; this is not a supplied hierarchy graph isomorphism. -/
def coordinates (m R : Nat) : CubeHierarchy.Coordinates
    (Base m R×Vertex (2*m))
    (AnchoredEmbedding.ProductRelation (BaseRelation m R) (@Adjacent (2*m)))
    (CubeHierarchy.dimension (2*m) R+2*m) where
  encode v:=CubeProduct.encode ((CubeHierarchy.tower (CubeHierarchy.identity (2*m)) R).encode v.1,v.2)
  decode w:=((CubeHierarchy.tower (CubeHierarchy.identity (2*m)) R).decode (CubeProduct.decode w).1,
    (CubeProduct.decode w).2)
  decode_encode v:=by simp only [CubeProduct.decode_encode,CubeHierarchy.Coordinates.decode_encode]
  encode_decode w:=by simp only [CubeHierarchy.Coordinates.encode_decode]; exact CubeProduct.encode_decode w
  adjacent u v:=by
    let I:=CubeHierarchy.tower (CubeHierarchy.identity (2*m)) R
    rw [CubeProduct.adjacent_iff]
    constructor
    · rintro (⟨hw,hr⟩|⟨hu,hr⟩)
      · exact Or.inl ⟨hw,(I.adjacent _ _).mp hr⟩
      · exact Or.inr ⟨CubeHierarchy.encode_injective I hu,hr⟩
    · rintro (⟨hw,hr⟩|⟨hu,hr⟩)
      · exact Or.inl ⟨hw,(I.adjacent _ _).mpr hr⟩
      · exact Or.inr ⟨congrArg I.encode hu,hr⟩

private def transportPaths {V : Type} {T : V→V→Prop} {n L : Nat}
    (I : CubeHierarchy.Coordinates V T n) (D : GraphPathDecomposition V T L) :
    GraphPathDecomposition (Vertex n) (@Adjacent n) L where
  Index:=D.Index
  indices:=D.indices
  vertices p t:=I.encode (D.vertices p t)
  simple p hp:=fun _ _ he=>D.simple p hp (CubeHierarchy.encode_injective I he)
  adjacent p hp t:=(I.adjacent _ _).mpr (D.adjacent p hp t)
  cover x y he:=by
    have hh : T (I.decode x) (I.decode y) := (I.adjacent _ _).mp
      (by simpa only [I.encode_decode] using he)
    obtain ⟨p,hp,t,ht⟩ := D.cover _ _ hh
    have hm := SubdividedWiggle.map_sameEdge I.encode ht
    simp only [I.encode_decode] at hm
    exact ⟨p,hp,t,hm⟩
  unique p q hp hq t s he:=by
    have hh := SubdividedWiggle.map_sameEdge I.decode he
    simp only [I.decode_encode] at hh
    exact D.unique p q hp hq t s hh

/-- Unconditional uniform two-binary-ones frontier, with actual simple paths
and exact undirected edge ownership in the genuine binary cube. -/
theorem frontier (m R : Nat) (hm : 1≤m) (hR : 1≤R) :
    HasPathDecomposition (2*m*(2^R+1))
      ((2^R+1)*2^(2*m*(2^R+1)-R-1)) := by
  have hx := exponent_room hm hR
  have ha : 2≤gridHalf m R := Nat.pow_le_pow_right (by decide : 1≤2)
    (show 1≤2*m*2^R-R-1 by omega)
  have hB4 : 4≤2^(2*m) := Nat.pow_le_pow_right (by decide : 1≤2) (show 2≤2*m by omega)
  have hs : 2≤2^R := Nat.pow_le_pow_right (by decide : 1≤2) hR
  have hev : 2^(2*m)%2=0 := by
    have he : 2*m=(2*m-1)+1 := by omega
    rw [he,Nat.pow_succ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)
  let D := AnchoredAssembly.productPathDecompositionExact (actualData m R hm hR) ha hB4 hev hs
  have H := GraphTarget.to_target (transportPaths (coordinates m R) D)
  have hn : CubeHierarchy.dimension (2*m) R+2*m=2*m*(2^R+1) := by
    rw [CubeHierarchy.dimension_formula,Nat.mul_add,Nat.mul_one]
  have hl : (2*gridHalf m R)*2^(2*m)*(2^R+1)/2=
      (2^R+1)*2^(2*m*(2^R+1)-R-1) := by
    rw [show (2*gridHalf m R)*2^(2*m)*(2^R+1)=
      (gridHalf m R*2^(2*m)*(2^R+1))*2 by ac_rfl,Nat.mul_div_cancel _ (by decide)]
    change 2^(2*m*2^R-R-1)*2^(2*m)*(2^R+1)=_
    rw [←Nat.pow_add,Nat.mul_comm]
    congr 2
    rw [Nat.mul_add,Nat.mul_one]
    omega
  change HasPathDecomposition (CubeHierarchy.dimension (2*m) R+2*m)
    ((2*gridHalf m R)*2^(2*m)*(2^R+1)/2) at H
  rw [hn,hl] at H
  exact H

#print axioms unique_phase
#print axioms factors
#print axioms position_zero_iff
#print axioms representative_owner
#print axioms factorData
#print axioms actualData
#print axioms frontier
end ErdePaths.TwoBitFrontier
