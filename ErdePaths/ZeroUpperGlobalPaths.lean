import ErdePaths.GraphTarget
import ErdePaths.ZeroUpperIsolatedPaths
import ErdePaths.SourceMarkedProduct


namespace ErdePaths.ZeroUpperGlobalPaths.Fold
open SquareLift SourceClock SourceProfile HierarchicalDecode ZeroUpperAACBase
set_option warn.classDefReducibility false
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

namespace Input
variable (I : ZeroUpperAACBase.Input) {j t : Nat} (ht : 0<t)
  (JD : HamiltonData.DecompositionData (Vertex j) (@Adjacent j) (I.m*(2^(I.k+0)-1)) (2*t) (by omega))

noncomputable def Host (n : I.Index) (x y : I.Y × Vertex j) : Prop :=
  SourceMarkedProduct.MarkedHost I.marks I.schedule (fun n=>I.Host n)
    (CubePairedPartition.cycles ht JD) n x y

private theorem base_partition (x y : I.Y) :
    SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=0) x y ↔
      ∃n : I.Index, I.Host n x y ∧ ∀n',I.Host n' x y→n'=n := by
  have hp:=ZeroUpperFactors.Actual.host_partition I.D I.he I.k I.hk I.room I.exceptional
    (HamiltonCommonLast.normalize I.HD I.last) I.z x y
  constructor
  · intro hh
    obtain ⟨q,hq,hu⟩:=hp.mp hh
    obtain ⟨n,hn⟩:=ZeroUpperGlobalMarks.sourceIndex_surjective I.k 0 I.hk q
    refine ⟨n,?_,?_⟩
    · change ZeroUpperFactors.Actual.Host _ _ _ _ _ _ _ _ (ZeroUpperGlobalMarks.sourceIndex I.k 0 n) x y
      rw [hn]; exact hq
    · intro n' hh'
      apply ZeroUpperGlobalMarks.sourceIndex_injective I.k 0 I.hk
      exact (hu _ hh').trans hn.symm
  · rintro ⟨n,hn,_⟩
    exact ZeroUpperFactors.host_subset I.D I.he I.k 0 I.hk
      (fun _=>ZeroUpperCodeOrigins.selectors I.k I.hk I.room I.exceptional)
      (fun _=>ZeroUpperCodeOrigins.odd I.k I.hk I.room I.exceptional) I.exceptional
      (fun f=>ZeroUpperCodeOrigins.data I.he I.k I.hk I.room I.exceptional (I.D.cycles f).toClockData)
      (HamiltonCommonLast.normalize I.HD I.last) I.z hn

private theorem base_cover {x y : I.Y}
    (he : SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=0) x y) :
    ∃n : I.Index, I.Host n x y := by
  obtain ⟨n,hn,_⟩:=(base_partition I x y).mp he
  exact ⟨n,hn⟩

private theorem base_relation {n : I.Index} {x y : I.Y} (hi : I.Host n x y) :
    SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=0) x y := by
  have hp:=ZeroUpperFactors.Actual.host_partition I.D I.he I.k I.hk I.room I.exceptional
    (HamiltonCommonLast.normalize I.HD I.last) I.z x y
  -- Use the established genuine host partition's forward ownership from its generic host subset.
  exact ZeroUpperFactors.host_subset I.D I.he I.k 0 I.hk
    (fun _=>ZeroUpperCodeOrigins.selectors I.k I.hk I.room I.exceptional)
    (fun _=>ZeroUpperCodeOrigins.odd I.k I.hk I.room I.exceptional) I.exceptional
    (fun f=>ZeroUpperCodeOrigins.data I.he I.k I.hk I.room I.exceptional (I.D.cycles f).toClockData)
    (HamiltonCommonLast.normalize I.HD I.last) I.z hi

private theorem base_unique {n n' : I.Index} {x y : I.Y}
    (hi : I.Host n x y) (hj : I.Host n' x y) : n=n' := by
  obtain ⟨q,hq,hu⟩:=(base_partition I x y).mp (base_relation I hi)
  exact (hu n hi).trans (hu n' hj).symm

private theorem base_loopfree (v : I.Y) :
    ¬SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=0) v v := by
  rintro (⟨_,hg⟩ | ⟨_,hh⟩)
  · exact adjacent_ne ((CubeHierarchy.sourceIso I.e I.k 0).adjacent v.1 v.1 |>.mpr hg) rfl
  · exact adjacent_ne hh rfl

/-- Actual global marked-host cover, from the genuine base partition and
internally derived noncrossing palette. -/
theorem host_cover {x y : I.Y×Vertex j}
    (he : AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=0)) (@Adjacent j) x y) :
    ∃n, Host I ht JD n x y := by
  rcases he with ⟨hj,hbase⟩|⟨hv,hj⟩
  · obtain ⟨n,hn⟩ := base_cover I hbase
    exact ⟨n,Or.inl ⟨hj,hn⟩⟩
  · obtain ⟨c,hc⟩ := CubePairedPartition.cover ht JD x.2 y.2 hj
    obtain ⟨o,ho,hl,_⟩ := SourceMarkedProduct.palette_owner I.marks I.schedule x.1 c
    refine ⟨o.1,Or.inr ⟨hv,o.2,ho,?_⟩⟩
    rw [hl]
    exact hc

theorem host_relation {n : I.Index} {x y : I.Y×Vertex j} (hi : Host I ht JD n x y) :
    AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=0)) (@Adjacent j) x y := by
  rcases hi with ⟨hj,hbase⟩|⟨hv,o,ho,hcycle⟩
  · exact Or.inl ⟨hj,base_relation I hbase⟩
  · exact Or.inr ⟨hv,CubePairedPartition.relation ht JD hcycle⟩

/-- Actual palette labels and genuine J factor separation force unique
physical hosts, including host intersections at repeated physical marks. -/
theorem host_unique {n n' : I.Index} {x y : I.Y×Vertex j}
    (hi : Host I ht JD n x y) (hj : Host I ht JD n' x y) : n=n' := by
  rcases hi with ⟨hx,hb⟩|⟨hv,o,ho,hc⟩
  · rcases hj with ⟨_,hb'⟩|⟨hv,_,_,_⟩
    · exact base_unique I hb hb'
    · have hh := base_relation I hb
      rw [hv] at hh
      exact False.elim (base_loopfree I _ hh)
  · rcases hj with ⟨_,hb'⟩|⟨_,o',ho',hc'⟩
    · have hh := base_relation I hb'
      rw [hv] at hh
      exact False.elim (base_loopfree I _ hh)
    · have hlabel := CubePairedPartition.unique ht JD hc hc'
      obtain ⟨owner,_,_,hu⟩ := SourceMarkedProduct.palette_owner I.marks I.schedule x.1 (I.schedule.labels n o)
      have hh := (hu ⟨n,o⟩ ho rfl).trans (hu ⟨n',o'⟩ ho' hlabel.symm).symm
      exact congrArg Sigma.fst hh

/-- The constructed actual long-word marked hosts partition the whole
physical product, with no supplied palette or host-owner premise. -/
theorem host_partition (x y : I.Y×Vertex j) :
    AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=0)) (@Adjacent j) x y ↔
    ∃n, Host I ht JD n x y ∧ ∀n', Host I ht JD n' x y→n'=n := by
  constructor
  · intro he
    obtain ⟨n,hn⟩ := host_cover I ht JD he
    exact ⟨n,hn,fun n' hn'=>host_unique I ht JD hn' hn⟩
  · rintro ⟨n,hn,_⟩
    exact host_relation I ht JD hn

/-- Exact identification of the local rotated geometric marked host with the
actual global palette host, using literal ordinal and layer lookup laws. -/
theorem local_host_iff (n : I.Index) (x y : I.Y × Vertex j) :
    AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
      (I.layers ht (CubePairedPartition.cycles ht JD) n) x y ↔ Host I ht JD n x y := by
  change AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
    (I.layers ht (CubePairedPartition.cycles ht JD) n) x y ↔
    SourceMarkedProduct.MarkedHost I.marks I.schedule (fun n => I.Host n)
      (CubePairedPartition.cycles ht JD) n x y
  constructor
  · rintro (⟨hx,hbase⟩ | ⟨q,hx,hy,hcycle⟩)
    · exact Or.inl ⟨hx,hbase⟩
    · refine Or.inr ⟨hx.trans hy.symm,Fin.cast (I.mark_card n) q,?_,?_⟩
      · exact (I.marked_lookup n q).symm.trans hx.symm
      · rw [I.layer_lookup] at hcycle
        exact hcycle
  · rintro (⟨hx,hbase⟩ | ⟨hx,o,hword,hcycle⟩)
    · exact Or.inl ⟨hx,hbase⟩
    · let q := Fin.cast (I.mark_card n).symm o
      have ho : Fin.cast (I.mark_card n) q=o := Fin.ext rfl
      have hmark : I.base n (AACIntervalSplit.markIndex (I.flag n) q)=(I.marks.word n)[o] :=
        I.marked_lookup n q
      have hxmark := (hmark.trans hword).symm
      refine Or.inr ⟨q,hxmark,hx.symm.trans hxmark,?_⟩
      rw [I.layer_lookup,ho]
      exact hcycle


abbrev Dimension (I : ZeroUpperAACBase.Input) (j : Nat) := I.e*2^(I.k+0+1)+I.d+j

def markCount (I : ZeroUpperAACBase.Input) : Nat :=
  (2*2^(I.k+0+1)-4)*(2^(I.e*2^(I.k+0+1)-1)/(2*2^(I.k+0+1)))*I.B

def totalLength (I : ZeroUpperAACBase.Input) (t : Nat) : Nat := t*(I.E+markCount I)

theorem length_eq (I : ZeroUpperAACBase.Input) (_ht : 0<t) (n : I.Index) :
    I.length (jR:=t) n=totalLength I t := I.fold_length n t

end Input
end ErdePaths.ZeroUpperGlobalPaths.Fold

namespace ErdePaths.ZeroUpperGlobalPaths
open SquareLift ZeroUpperAACBase ZeroUpperGlobalPaths.Fold
set_option warn.classDefReducibility false
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Reindex only a proved path length equality. -/
def castLength {V R L M} (he : L=M) (D : GraphPathDecomposition V R L) :
    GraphPathDecomposition V R M := by subst M; exact D

namespace Input
variable (I : ZeroUpperAACBase.Input)
  {j t : Nat} (ht : 0<t) (h2 : 2≤t)
  (JD : HamiltonData.DecompositionData (Vertex j) (@Adjacent j) (I.m*(2^(I.k+0)-1)) (2*t) (by omega))

noncomputable def localPaths (n : I.Index) : GraphPathDecomposition (I.Y×Vertex j)
    (ZeroUpperGlobalPaths.Fold.Input.Host I ht JD n) (ZeroUpperGlobalPaths.Fold.Input.totalLength I t) := by
  let D := castLength (ZeroUpperGlobalPaths.Fold.Input.length_eq I ht n)
    (ZeroUpperIsolatedPaths.paths ht I h2 (CubePairedPartition.cycles ht JD) n)
  exact {
    Index:=D.Index, indices:=D.indices, vertices:=D.vertices
    simple:=D.simple
    adjacent:=fun p hp k=>(ZeroUpperGlobalPaths.Fold.Input.local_host_iff I ht JD n _ _).mp (D.adjacent p hp k)
    cover:=fun x y he=>D.cover x y ((ZeroUpperGlobalPaths.Fold.Input.local_host_iff I ht JD n _ _).mpr he)
    unique:=D.unique }

abbrev Index := (n : I.Index) × (localPaths I ht h2 JD n).Index

noncomputable def indices : List (Index I ht h2 JD) :=
  (List.finRange (I.m*2^(I.k+0+1))).flatMap fun n=>
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
    (hh : ZeroUpperGlobalPaths.Fold.Input.Host I ht JD n x y) (he : SameEdge (x,y) (u,v)) :
    ZeroUpperGlobalPaths.Fold.Input.Host I ht JD n u v := by
  have hl := (ZeroUpperGlobalPaths.Fold.Input.local_host_iff I ht JD n x y).mpr hh
  rcases he with he|he
  · cases he; exact hh
  · have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp only at hx hy
    rw [←hy,←hx]
    apply (ZeroUpperGlobalPaths.Fold.Input.local_host_iff I ht JD n y x).mp
    rcases hl with ⟨hx,hbase⟩|⟨q,hx,hy,a,p,hedge⟩
    · obtain ⟨k,hk⟩ := (I.host_cover n _ _).mp hbase
      exact Or.inl ⟨hx.symm,(I.host_cover n _ _).mpr ⟨k,sameEdge_trans hk (Or.inr rfl)⟩⟩
    · exact Or.inr ⟨q,hy,hx,a,p,sameEdge_trans hedge (Or.inr rfl)⟩

/-- Actual opened local paths partition the ENTIRE physical cube product.
Global ownership is derived from the actual palette hosts. -/
noncomputable def physical : GraphPathDecomposition (I.Y×Vertex j)
    (AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=0)) (@Adjacent j))
    (ZeroUpperGlobalPaths.Fold.Input.totalLength I t) where
  Index:=Index I ht h2 JD
  indices:=indices I ht h2 JD
  vertices:=fun p=>(localPaths I ht h2 JD p.1).vertices p.2
  simple:=fun p hp=>(localPaths I ht h2 JD p.1).simple p.2 ((mem_indices I ht h2 JD p).mp hp)
  adjacent:=by
    intro p hp k
    exact ZeroUpperGlobalPaths.Fold.Input.host_relation I ht JD
      ((localPaths I ht h2 JD p.1).adjacent p.2 ((mem_indices I ht h2 JD p).mp hp) k)
  cover:=by
    intro x y he
    obtain ⟨n,hn⟩ := ZeroUpperGlobalPaths.Fold.Input.host_cover I ht JD he
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
    have hnn := ZeroUpperGlobalPaths.Fold.Input.host_unique I ht JD hsame hn'
    subst n'
    have hh := (localPaths I ht h2 JD n).unique p q hp' hq' k l he
    exact ⟨by rw [hh.1],hh.2⟩

/-- Faithful binary-coordinate transport of the actual global simple paths. -/
noncomputable def cube : GraphPathDecomposition
    (Vertex (ZeroUpperGlobalPaths.Fold.Input.Dimension I j)) (@Adjacent _) (ZeroUpperGlobalPaths.Fold.Input.totalLength I t) := by
  let D := physical I ht h2 JD
  exact {
    Index:=D.Index, indices:=D.indices
    vertices:=fun p k=>SourceMarkedProduct.cubeEncode I.k 0 (D.vertices p k)
    simple:=by
      intro p hp k l he
      have hh := congrArg (SourceMarkedProduct.cubeDecode I.k 0) he
      simp only [SourceMarkedProduct.cubeDecode_encode] at hh
      exact D.simple p hp hh
    adjacent:=fun p hp k=>(SourceMarkedProduct.cube_adjacent_iff I.k 0 _ _).mpr (D.adjacent p hp k)
    cover:=by
      intro x y he
      have hh := SourceMarkedProduct.cube_adjacent_iff I.k 0
        (SourceMarkedProduct.cubeDecode I.k 0 x) (SourceMarkedProduct.cubeDecode I.k 0 y)
      rw [SourceMarkedProduct.cubeEncode_decode,SourceMarkedProduct.cubeEncode_decode] at hh
      obtain ⟨p,hp,k,hk⟩ := D.cover _ _ (hh.mp he)
      have hmap := SubdividedWiggle.map_sameEdge (SourceMarkedProduct.cubeEncode I.k 0) hk
      simp only [SourceMarkedProduct.cubeEncode_decode] at hmap
      exact ⟨p,hp,k,hmap⟩
    unique:=by
      intro p q hp hq k l he
      have hh := SubdividedWiggle.map_sameEdge (SourceMarkedProduct.cubeDecode I.k 0) he
      simp only [SourceMarkedProduct.cubeDecode_encode] at hh
      exact D.unique p q hp hq k l hh }

#print axioms cube
end Input
end ErdePaths.ZeroUpperGlobalPaths
