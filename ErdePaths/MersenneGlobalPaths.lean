import ErdePaths.MersenneIsolatedPaths
import ErdePaths.MersenneGlobalFold
import ErdePaths.GraphTarget

namespace ErdePaths.MersenneGlobalPaths
open SquareLift MersenneAACBase MersenneGlobalFold
set_option warn.classDefReducibility false
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Reindex only a proved path length equality. -/
def castLength {V R L M} (he : L=M) (D : GraphPathDecomposition V R L) :
    GraphPathDecomposition V R M := by subst M; exact D

namespace Input
variable (I : MersenneAACBase.Input)
  {j t : Nat} (ht : 0<t) (h2 : 2≤t)
  (JD : HamiltonData.DecompositionData (Vertex j) (@Adjacent j) (I.m*(2^(I.k+I.h)-1)) (2*t) (by omega))

noncomputable def localPaths (n : I.Index) : GraphPathDecomposition (I.Y×Vertex j)
    (MersenneGlobalFold.Input.Host I ht JD n) (MersenneGlobalFold.Input.totalLength I t) := by
  let D := castLength (MersenneGlobalFold.Input.length_eq I ht n)
    (MersenneIsolatedPaths.paths ht I h2 (CubePairedPartition.cycles ht JD) n)
  exact {
    Index:=D.Index, indices:=D.indices, vertices:=D.vertices
    simple:=D.simple
    adjacent:=fun p hp k=>(MersenneGlobalFold.Input.local_host_iff I ht JD n _ _).mp (D.adjacent p hp k)
    cover:=fun x y he=>D.cover x y ((MersenneGlobalFold.Input.local_host_iff I ht JD n _ _).mpr he)
    unique:=D.unique }

abbrev Index := (n : I.Index) × (localPaths I ht h2 JD n).Index

noncomputable def indices : List (Index I ht h2 JD) :=
  (List.finRange (I.m*2^(I.k+I.h+1))).flatMap fun n=>
    ((localPaths I ht h2 JD n).indices).map fun p=>⟨n,p⟩

theorem mem_indices (p : Index I ht h2 JD) :
    p∈indices I ht h2 JD ↔ p.2∈(localPaths I ht h2 JD p.1).indices := by
  rcases p with ⟨i,o⟩
  constructor
  · intro hp
    obtain ⟨n,_,hm⟩ := List.mem_flatMap.mp hp
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
    have hn : n=i := congrArg Sigma.fst he
    subst n
    have hq' : q=o := eq_of_heq (Sigma.mk.inj he).2
    rw [←hq']; exact hq
  · intro hp
    exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨o,hp,rfl⟩⟩

set_option linter.unusedSectionVars false in
private theorem host_sameEdge (n : I.Index) {x y u v : I.Y×Vertex j}
    (hh : MersenneGlobalFold.Input.Host I ht JD n x y) (he : SameEdge (x,y) (u,v)) :
    MersenneGlobalFold.Input.Host I ht JD n u v := by
  have hl := (MersenneGlobalFold.Input.local_host_iff I ht JD n x y).mpr hh
  rcases he with he|he
  · cases he; exact hh
  · have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only at hx hy
    rw [←hy,←hx]
    apply (MersenneGlobalFold.Input.local_host_iff I ht JD n y x).mp
    rcases hl with ⟨hx,hbase⟩|⟨q,hx,hy,a,p,hedge⟩
    · obtain ⟨k,hk⟩ := (I.host_cover n _ _).mp hbase
      exact Or.inl ⟨hx.symm,(I.host_cover n _ _).mpr ⟨k,sameEdge_trans hk (Or.inr rfl)⟩⟩
    · exact Or.inr ⟨q,hy,hx,a,p,sameEdge_trans hedge (Or.inr rfl)⟩

/-- Actual opened local paths partition the ENTIRE physical cube product.
Global ownership is derived from the actual palette hosts. -/
noncomputable def physical : GraphPathDecomposition (I.Y×Vertex j)
    (AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h)) (@Adjacent j))
    (MersenneGlobalFold.Input.totalLength I t) where
  Index:=Index I ht h2 JD
  indices:=indices I ht h2 JD
  vertices:=fun p=>(localPaths I ht h2 JD p.1).vertices p.2
  simple:=fun p hp=>(localPaths I ht h2 JD p.1).simple p.2 ((mem_indices I ht h2 JD p).mp hp)
  adjacent:=by
    intro p hp k
    exact MersenneGlobalFold.Input.host_relation I ht JD
      ((localPaths I ht h2 JD p.1).adjacent p.2 ((mem_indices I ht h2 JD p).mp hp) k)
  cover:=by
    intro x y he
    obtain ⟨n,hn⟩ := MersenneGlobalFold.Input.host_cover I ht JD he
    obtain ⟨p,hp,k,hk⟩ := (localPaths I ht h2 JD n).cover x y hn
    exact ⟨⟨n,p⟩,(mem_indices I ht h2 JD ⟨n,p⟩).mpr hp,k,hk⟩
  unique:=by
    intro p q hp hq k l he
    rcases p with ⟨n,p⟩; rcases q with ⟨n',q⟩
    have hp' := (mem_indices I ht h2 JD ⟨n,p⟩).mp hp
    have hq' := (mem_indices I ht h2 JD ⟨n',q⟩).mp hq
    have hn := (localPaths I ht h2 JD n).adjacent p hp' k
    have hn' := (localPaths I ht h2 JD n').adjacent q hq' l
    have hsame := host_sameEdge I ht h2 JD n hn he
    have hnn := MersenneGlobalFold.Input.host_unique I ht JD hsame hn'
    subst n'
    have hh := (localPaths I ht h2 JD n).unique p q hp' hq' k l he
    exact ⟨by rw [hh.1],hh.2⟩

/-- Faithful binary-coordinate transport of the actual global simple paths. -/
noncomputable def cube : GraphPathDecomposition
    (Vertex (MersenneGlobalFold.Input.Dimension I j)) (@Adjacent _) (MersenneGlobalFold.Input.totalLength I t) := by
  let D := physical I ht h2 JD
  exact {
    Index:=D.Index, indices:=D.indices
    vertices:=fun p k=>SourceMarkedProduct.cubeEncode I.k I.h (D.vertices p k)
    simple:=by
      intro p hp k l he
      have hh := congrArg (SourceMarkedProduct.cubeDecode I.k I.h) he
      simp only [SourceMarkedProduct.cubeDecode_encode] at hh
      exact D.simple p hp hh
    adjacent:=fun p hp k=>(SourceMarkedProduct.cube_adjacent_iff I.k I.h _ _).mpr (D.adjacent p hp k)
    cover:=by
      intro x y he
      have hh := SourceMarkedProduct.cube_adjacent_iff I.k I.h
        (SourceMarkedProduct.cubeDecode I.k I.h x) (SourceMarkedProduct.cubeDecode I.k I.h y)
      rw [SourceMarkedProduct.cubeEncode_decode,SourceMarkedProduct.cubeEncode_decode] at hh
      obtain ⟨p,hp,k,hk⟩ := D.cover _ _ (hh.mp he)
      have hmap := SubdividedWiggle.map_sameEdge (SourceMarkedProduct.cubeEncode I.k I.h) hk
      simp only [SourceMarkedProduct.cubeEncode_decode] at hmap
      exact ⟨p,hp,k,hmap⟩
    unique:=by
      intro p q hp hq k l he
      have hh := SubdividedWiggle.map_sameEdge (SourceMarkedProduct.cubeDecode I.k I.h) he
      simp only [SourceMarkedProduct.cubeDecode_encode] at hh
      exact D.unique p q hp hq k l hh }

#print axioms cube
end Input
end ErdePaths.MersenneGlobalPaths
