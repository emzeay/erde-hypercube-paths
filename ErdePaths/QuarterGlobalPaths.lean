import ErdePaths.QuarterIsolatedPaths
import ErdePaths.SourceMarkedProduct
import ErdePaths.GraphTarget

namespace ErdePaths.QuarterGlobalPaths
open SquareLift QuarterAACBase QuarterAACBase
set_option warn.classDefReducibility false
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Reindex only a proved path length equality. -/
def castLength {V R L M} (he : L=M) (D : GraphPathDecomposition V R L) :
    GraphPathDecomposition V R M := by subst M; exact D

namespace Input
variable (I : QuarterAACBase.Input)
  {j t : Nat} (ht : 0<t) (h2 : 2≤t)
  (JD : HamiltonData.DecompositionData (Vertex j) (@Adjacent j) (I.m*1) (2*t) (Nat.mul_pos (by decide) ht))

abbrev Dimension (I : QuarterAACBase.Input) (j : Nat) := I.e*2^(1+0+1)+I.d+j

def totalLength (I : QuarterAACBase.Input) (t : Nat) := t*(I.E+(I.K/2)*I.B)

include ht h2 JD in
theorem length_eq (n : I.Index) : I.length (jR:=t) n=totalLength I t := by
  rw [(I.decomposition ht h2 (CubePairedPartition.cycles ht JD) n).2.2.2.2,I.word_length_exact]
  rfl

noncomputable def Host (n : I.Index) : (I.Y×Vertex j)→(I.Y×Vertex j)→Prop :=
  SourceMarkedProduct.MarkedHost I.marks I.schedule (fun n=>I.Host n) (CubePairedPartition.cycles ht JD) n

theorem local_host_iff (n : I.Index) (x y : I.Y×Vertex j) :
    AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
      (I.layers ht (CubePairedPartition.cycles ht JD) n) x y ↔ Host I ht JD n x y := by
  constructor
  · rintro (⟨hx,hbase⟩ | ⟨q,hx,hy,hcycle⟩)
    · exact Or.inl ⟨hx,hbase⟩
    · refine Or.inr ⟨hx.trans hy.symm,Fin.cast (I.mark_card n) q,?_,?_⟩
      · exact (I.marked_lookup n q).symm.trans hx.symm
      · rw [I.layer_lookup] at hcycle; exact hcycle
  · rintro (⟨hx,hbase⟩ | ⟨hx,o,hword,hcycle⟩)
    · exact Or.inl ⟨hx,hbase⟩
    · let q := Fin.cast (I.mark_card n).symm o
      have ho : Fin.cast (I.mark_card n) q=o := Fin.ext rfl
      have hm : I.base n (AACIntervalSplit.markIndex (I.flag n) q)=(I.marks.word n)[o] := I.marked_lookup n q
      have hxmark := (hm.trans hword).symm
      refine Or.inr ⟨q,hxmark,hx.symm.trans hxmark,?_⟩
      rw [I.layer_lookup,ho]; exact hcycle

private theorem base_partition (x y : I.Y) :
    SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=1) (h:=0) x y ↔
      ∃n : I.Index,I.Host n x y ∧ ∀n',I.Host n' x y→n'=n := by
  have hh := QuarterFactorGeometry.host_partition I.D I.he (HamiltonCommonLast.normalize I.HD I.last)
    (⟨1,by decide⟩ : Fin 2) x y
  constructor
  · intro hxy
    obtain ⟨i,hi,hu⟩ := hh.mp hxy
    obtain ⟨n,hn⟩ := SourceGlobalMarks.sourceIndex_surjective (m:=I.m) 1 0 1 (by decide) i
    refine ⟨n,?_,?_⟩
    · change QuarterFactorGeometry.Host _ _ _ _ (I.factor n) x y
      rw [show I.factor n=i from hn]; exact hi
    · intro n' hn'
      apply SourceGlobalMarks.sourceIndex_injective 1 0 1 (by decide)
      exact (hu _ hn').trans hn.symm
  · rintro ⟨n,hn,_⟩
    exact OriginFactors.host_subset I.D I.he 1 0 (by decide)
      (fun _=>QuarterProfileOrigins.selectors I.he) (fun _=>QuarterProfileOrigins.odd I.he)
      (fun f=>QuarterSourceOrigins.data I.he (I.D.cycles f).toClockData)
      (HamiltonCommonLast.normalize I.HD I.last) (⟨1,by decide⟩ : Fin 2) hn

private theorem base_relation {n : I.Index} {x y : I.Y} (hh : I.Host n x y) :
    SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=1) (h:=0) x y := by
  have hp := QuarterFactorGeometry.host_partition I.D I.he (HamiltonCommonLast.normalize I.HD I.last)
    (⟨1,by decide⟩ : Fin 2) x y
  -- The generic host theorem supplies subset directly, without choosing another owner.
  exact OriginFactors.host_subset I.D I.he 1 0 (by decide)
    (fun _=>QuarterProfileOrigins.selectors I.he) (fun _=>QuarterProfileOrigins.odd I.he)
    (fun f=>QuarterSourceOrigins.data I.he (I.D.cycles f).toClockData)
    (HamiltonCommonLast.normalize I.HD I.last) (⟨1,by decide⟩ : Fin 2) hh

theorem host_relation {n : I.Index} {x y : I.Y×Vertex j} (hh : Host I ht JD n x y) :
    AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=1) (h:=0)) (@Adjacent j) x y := by
  rcases hh with ⟨he,hb⟩ | ⟨he,o,hm,hc⟩
  · exact Or.inl ⟨he,base_relation I hb⟩
  · exact Or.inr ⟨he,CubePairedPartition.relation ht JD hc⟩

theorem host_cover {x y : I.Y×Vertex j} (hh : AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=1) (h:=0)) (@Adjacent j) x y) :
    ∃n,Host I ht JD n x y := by
  rcases hh with ⟨he,hb⟩ | ⟨he,hc⟩
  · obtain ⟨n,hn,_⟩ := (base_partition I _ _).mp hb
    exact ⟨n,Or.inl ⟨he,hn⟩⟩
  · obtain ⟨c,hc⟩ := CubePairedPartition.cover ht JD _ _ hc
    obtain ⟨o,ho,hl,_⟩ := SourceMarkedProduct.palette_owner I.marks I.schedule x.1 c
    refine ⟨o.1,Or.inr ⟨he,o.2,ho,?_⟩⟩
    rw [hl]; exact hc

private theorem base_loopfree (v : I.Y) :
    ¬SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=1) (h:=0) v v := by
  rintro (⟨_,hg⟩ | ⟨_,hh⟩)
  · exact adjacent_ne ((CubeHierarchy.sourceIso I.e 1 0).adjacent v.1 v.1 |>.mpr hg) rfl
  · exact adjacent_ne hh rfl

theorem host_unique {n n' : I.Index} {x y : I.Y×Vertex j}
    (hn : Host I ht JD n x y) (hn' : Host I ht JD n' x y) : n=n' := by
  rcases hn with ⟨hx,hb⟩ | ⟨hv,o,hm,hc⟩
  · rcases hn' with ⟨_,hb'⟩ | ⟨hv,_,_,_⟩
    · obtain ⟨owner,_,hu⟩ := (base_partition I _ _).mp (base_relation I hb)
      exact (hu _ hb).trans (hu _ hb').symm
    · have hh := base_relation I hb
      rw [hv] at hh
      exact False.elim (base_loopfree I _ hh)
  · rcases hn' with ⟨_,hb⟩ | ⟨_,o',hm',hc'⟩
    · have hh := base_relation I hb
      rw [hv] at hh
      exact False.elim (base_loopfree I _ hh)
    · have he := CubePairedPartition.unique ht JD hc hc'
      obtain ⟨owner,_,_,hu⟩ := SourceMarkedProduct.palette_owner I.marks I.schedule x.1 (I.schedule.labels n o)
      exact congrArg Sigma.fst ((hu ⟨n,o⟩ hm rfl).trans (hu ⟨n',o'⟩ hm' he.symm).symm)

noncomputable def localPaths (n : I.Index) : GraphPathDecomposition (I.Y×Vertex j)
    (Host I ht JD n) (totalLength I t) := by
  let D := castLength (length_eq I ht h2 JD n)
    (QuarterIsolatedPaths.paths ht I h2 (CubePairedPartition.cycles ht JD) n)
  exact {
    Index:=D.Index, indices:=D.indices, vertices:=D.vertices
    simple:=D.simple
    adjacent:=fun p hp k=>(local_host_iff I ht JD n _ _).mp (D.adjacent p hp k)
    cover:=fun x y he=>D.cover x y ((local_host_iff I ht JD n _ _).mpr he)
    unique:=D.unique }

abbrev Index := (n : I.Index) × (localPaths I ht h2 JD n).Index

noncomputable def indices : List (Index I ht h2 JD) :=
  (List.finRange (I.m*4)).flatMap fun n=>
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
    (hh : Host I ht JD n x y) (he : SameEdge (x,y) (u,v)) :
    Host I ht JD n u v := by
  have hl := (local_host_iff I ht JD n x y).mpr hh
  rcases he with he|he
  · cases he; exact hh
  · have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only at hx hy
    rw [←hy,←hx]
    apply (local_host_iff I ht JD n y x).mp
    rcases hl with ⟨hx,hbase⟩|⟨q,hx,hy,a,p,hedge⟩
    · obtain ⟨k,hk⟩ := (I.host_cover n _ _).mp hbase
      exact Or.inl ⟨hx.symm,(I.host_cover n _ _).mpr ⟨k,sameEdge_trans hk (Or.inr rfl)⟩⟩
    · exact Or.inr ⟨q,hy,hx,a,p,sameEdge_trans hedge (Or.inr rfl)⟩

/-- Actual opened local paths partition the ENTIRE physical cube product.
Global ownership is derived from the actual palette hosts. -/
noncomputable def physical : GraphPathDecomposition (I.Y×Vertex j)
    (AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=1) (h:=0)) (@Adjacent j))
    (totalLength I t) where
  Index:=Index I ht h2 JD
  indices:=indices I ht h2 JD
  vertices:=fun p=>(localPaths I ht h2 JD p.1).vertices p.2
  simple:=fun p hp=>(localPaths I ht h2 JD p.1).simple p.2 ((mem_indices I ht h2 JD p).mp hp)
  adjacent:=by
    intro p hp k
    exact host_relation I ht JD
      ((localPaths I ht h2 JD p.1).adjacent p.2 ((mem_indices I ht h2 JD p).mp hp) k)
  cover:=by
    intro x y he
    obtain ⟨n,hn⟩ := host_cover I ht JD he
    obtain ⟨p,hp,k,hk⟩ := (localPaths I ht h2 JD n).cover x y hn
    exact ⟨⟨n,p⟩,(mem_indices I ht h2 JD ⟨n,p⟩).mpr hp,k,hk⟩
  unique:=by
    intro p q hp hq k l he
    rcases p with ⟨n,p⟩; rcases q with ⟨n',q⟩
    have hp' := (mem_indices I ht h2 JD ⟨n,p⟩).mp hp
    have hq' := (mem_indices I ht h2 JD ⟨n',q⟩).mp hq
    have hn := (localPaths I ht h2 JD n).adjacent p hp' k
    have hn' := (localPaths I ht h2 JD n').adjacent q hq' l
    have hsame := host_sameEdge I ht JD n hn he
    have hnn := host_unique I ht JD hsame hn'
    subst n'
    have hh := (localPaths I ht h2 JD n).unique p q hp' hq' k l he
    exact ⟨by rw [hh.1],hh.2⟩

/-- Faithful binary-coordinate transport of the actual global simple paths. -/
noncomputable def cube : GraphPathDecomposition
    (Vertex (Dimension I j)) (@Adjacent _) (totalLength I t) := by
  let D := physical I ht h2 JD
  exact {
    Index:=D.Index, indices:=D.indices
    vertices:=fun p k=>SourceMarkedProduct.cubeEncode 1 0 (D.vertices p k)
    simple:=by
      intro p hp k l he
      have hh := congrArg (SourceMarkedProduct.cubeDecode 1 0) he
      simp only [SourceMarkedProduct.cubeDecode_encode] at hh
      exact D.simple p hp hh
    adjacent:=fun p hp k=>(SourceMarkedProduct.cube_adjacent_iff 1 0 _ _).mpr (D.adjacent p hp k)
    cover:=by
      intro x y he
      have hh := SourceMarkedProduct.cube_adjacent_iff 1 0
        (SourceMarkedProduct.cubeDecode 1 0 x) (SourceMarkedProduct.cubeDecode 1 0 y)
      rw [SourceMarkedProduct.cubeEncode_decode,SourceMarkedProduct.cubeEncode_decode] at hh
      obtain ⟨p,hp,k,hk⟩ := D.cover _ _ (hh.mp he)
      have hmap := SubdividedWiggle.map_sameEdge (SourceMarkedProduct.cubeEncode 1 0) hk
      simp only [SourceMarkedProduct.cubeEncode_decode] at hmap
      exact ⟨p,hp,k,hmap⟩
    unique:=by
      intro p q hp hq k l he
      have hh := SubdividedWiggle.map_sameEdge (SourceMarkedProduct.cubeDecode 1 0) he
      simp only [SourceMarkedProduct.cubeDecode_encode] at hh
      exact D.unique p q hp hq k l hh }

#print axioms cube
end Input
end ErdePaths.QuarterGlobalPaths
