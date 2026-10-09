import ErdePaths.MersenneAACBase
import ErdePaths.SourceMarkedProduct


namespace ErdePaths.MersenneGlobalFold
open SquareLift SourceClock SourceProfile HierarchicalDecode MersenneAACBase
set_option warn.classDefReducibility false
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

namespace Input
variable (I : MersenneAACBase.Input) {j t : Nat} (ht : 0<t)
  (JD : HamiltonData.DecompositionData (Vertex j) (@Adjacent j) (I.m*(2^(I.k+I.h)-1)) (2*t) (by omega))

noncomputable def Host (n : I.Index) (x y : I.Y × Vertex j) : Prop :=
  SourceMarkedProduct.MarkedHost I.marks I.schedule (fun n=>I.Host n)
    (CubePairedPartition.cycles ht JD) n x y

private theorem base_cover {x y : I.Y}
    (he : SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h) x y) :
    ∃n : I.Index, I.Host n x y := by
  obtain ⟨q,hq⟩ := MersenneOrientedFactors.host_cover I.D I.he I.k I.h I.hk I.hh I.room
    I.S I.ho I.balance I.exceptional (HamiltonCommonLast.normalize I.HD I.last) I.z he
  obtain ⟨n,hn⟩ := MersenneGlobalMarks.sourceIndex_surjective I.k I.h I.hk q
  refine ⟨n,?_⟩
  change MersenneOrientedFactors.Host _ _ _ _ _ _ _ _ _ _ _ _ _
    (MersenneGlobalMarks.sourceIndex I.k I.h n) x y
  rw [hn]
  exact hq

private theorem base_relation {n : I.Index} {x y : I.Y} (hi : I.Host n x y) :
    SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h) x y :=
  MersenneOrientedFactors.host_subset I.D I.he I.k I.h I.hk I.hh I.room I.S I.ho I.balance
    I.exceptional (HamiltonCommonLast.normalize I.HD I.last) I.z hi

private theorem base_unique {n n' : I.Index} {x y : I.Y}
    (hi : I.Host n x y) (hj : I.Host n' x y) : n=n' :=
  MersenneGlobalMarks.sourceIndex_injective I.k I.h I.hk
    (MersenneOrientedFactors.host_unique I.D I.he I.k I.h I.hk I.hh I.room I.S I.ho I.balance
      I.exceptional (HamiltonCommonLast.normalize I.HD I.last) I.z hi hj)

private theorem base_loopfree (v : I.Y) :
    ¬SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h) v v := by
  rintro (⟨_,hg⟩ | ⟨_,hh⟩)
  · exact adjacent_ne ((CubeHierarchy.sourceIso I.e I.k I.h).adjacent v.1 v.1 |>.mpr hg) rfl
  · exact adjacent_ne hh rfl

/-- Actual global marked-host cover, from the genuine base partition and
internally derived noncrossing palette. -/
theorem host_cover {x y : I.Y×Vertex j}
    (he : AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h)) (@Adjacent j) x y) :
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
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h)) (@Adjacent j) x y := by
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
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h)) (@Adjacent j) x y ↔
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

/-- Every actual local folded edge belongs to its actual global input host. -/
theorem tour_host (h2 : 2≤t) (n : I.Index) (color : Bool)
    (p : Fin (I.length (jR:=t) n)) : Host I ht JD n
      (I.tour ht (CubePairedPartition.cycles ht JD) n color p)
      (I.tour ht (CubePairedPartition.cycles ht JD) n color (successor (I.length_pos ht n) p)) :=
  (local_host_iff I ht JD n _ _).mp
    ((I.decomposition ht h2 (CubePairedPartition.cycles ht JD) n).2.2.2.1 color p)

private theorem host_symm (n : I.Index) {x y : I.Y × Vertex j} (hh : Host I ht JD n x y) :
    Host I ht JD n y x := by
  apply (local_host_iff I ht JD n y x).mp
  have hp := (local_host_iff I ht JD n x y).mpr hh
  rcases hp with ⟨hx,hbase⟩ | ⟨q,hx,hy,a,p,hcycle⟩
  · obtain ⟨k,hk⟩ := (I.host_cover n _ _).mp hbase
    exact Or.inl ⟨hx.symm,(I.host_cover n _ _).mpr
      ⟨k,SquareLift.sameEdge_trans hk (Or.inr rfl)⟩⟩
  · exact Or.inr ⟨q,hy,hx,a,p,SquareLift.sameEdge_trans hcycle (Or.inr rfl)⟩

/-- Two actual numeric simple cycles per host partition the ENTIRE genuine
source × H × J physical product edge relation. -/
theorem physical_decomposition (h2 : 2≤t) :
    let tours := I.tour ht (CubePairedPartition.cycles ht JD)
    (∀n color, Function.Injective (tours n color)) ∧
    (∀x y, AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h)) (@Adjacent j) x y →
      ∃n color p, SameEdge (tours n color p,tours n color (successor (I.length_pos ht n) p)) (x,y)) ∧
    (∀n color p n' color' p', SameEdge
      (tours n color p,tours n color (successor (I.length_pos ht n) p))
      (tours n' color' p',tours n' color' (successor (I.length_pos ht n') p')) →
      ∃hn : n=n', color=color' ∧ Fin.cast (congrArg (I.length (jR:=t)) hn) p=p') ∧
    (∀n color p, AnchoredEmbedding.ProductRelation
      (SourceMarkedProduct.BaseRelation (e:=I.e) (d:=I.d) (a:=I.k) (h:=I.h)) (@Adjacent j)
      (tours n color p) (tours n color (successor (I.length_pos ht n) p))) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro n color
    exact (I.decomposition ht h2 (CubePairedPartition.cycles ht JD) n).1 color
  · intro x y hedge
    obtain ⟨n,hn⟩ := host_cover I ht JD hedge
    have hl := (local_host_iff I ht JD n x y).mpr hn
    obtain ⟨color,p,hp⟩ := (I.decomposition ht h2 (CubePairedPartition.cycles ht JD) n).2.1 x y hl
    exact ⟨n,color,p,hp⟩
  · intro n color p n' color' p' he
    have hi := tour_host I ht JD h2 n color p
    have hj := tour_host I ht JD h2 n' color' p'
    have hj' : Host I ht JD n'
        (I.tour ht (CubePairedPartition.cycles ht JD) n color p)
        (I.tour ht (CubePairedPartition.cycles ht JD) n color (successor (I.length_pos ht n) p)) := by
      rcases he with he | he
      · have hf := congrArg Prod.fst he
        have hs := congrArg Prod.snd he
        dsimp only at hf hs
        rw [hf,hs]
        exact hj
      · have hf := congrArg Prod.fst he
        have hs := congrArg Prod.snd he
        dsimp only at hf hs
        rw [hf,hs]
        exact host_symm I ht JD n' hj
    have hn := host_unique I ht JD hi hj'
    subst n'
    have hp := (I.decomposition ht h2 (CubePairedPartition.cycles ht JD) n).2.2.1 color p color' p' he
    exact ⟨rfl,hp.1,hp.2⟩
  · intro n color p
    exact host_relation I ht JD (tour_host I ht JD h2 n color p)


abbrev Dimension (I : MersenneAACBase.Input) (j : Nat) := I.e*2^(I.k+I.h+1)+I.d+j

/-- Literal actual binary-coordinate tours, two per canonical source host. -/
noncomputable def cubeTour (n : I.Index) (color : Bool) :
    Fin (I.length (jR:=t) n)→Vertex (Dimension I j) := fun p =>
  SourceMarkedProduct.cubeEncode I.k I.h (I.tour ht (CubePairedPartition.cycles ht JD) n color p)

/-- Complete actual cube edge ledger for the constructed simple tours.
No graph-cover, descriptor or return assumption survives. -/
theorem cube_decomposition (h2 : 2≤t) :
    (∀n color, Function.Injective (cubeTour I ht JD n color)) ∧
    (∀x y : Vertex (Dimension I j), Adjacent x y →
      ∃n color p, SameEdge (cubeTour I ht JD n color p,
        cubeTour I ht JD n color (successor (I.length_pos ht n) p)) (x,y)) ∧
    (∀n color p n' color' p', SameEdge
      (cubeTour I ht JD n color p,cubeTour I ht JD n color (successor (I.length_pos ht n) p))
      (cubeTour I ht JD n' color' p',cubeTour I ht JD n' color' (successor (I.length_pos ht n') p')) →
      ∃hn : n=n', color=color' ∧ Fin.cast (congrArg (I.length (jR:=t)) hn) p=p') ∧
    (∀n color p, Adjacent (cubeTour I ht JD n color p)
      (cubeTour I ht JD n color (successor (I.length_pos ht n) p))) := by
  have hp := physical_decomposition I ht JD h2
  refine ⟨?_,?_,?_,?_⟩
  · intro n color p q he
    have hh := congrArg (SourceMarkedProduct.cubeDecode I.k I.h) he
    simp only [cubeTour,SourceMarkedProduct.cubeDecode_encode] at hh
    exact hp.1 n color hh
  · intro x y hedge
    have hh := SourceMarkedProduct.cube_adjacent_iff I.k I.h
      (SourceMarkedProduct.cubeDecode I.k I.h x) (SourceMarkedProduct.cubeDecode I.k I.h y)
    rw [SourceMarkedProduct.cubeEncode_decode,SourceMarkedProduct.cubeEncode_decode] at hh
    obtain ⟨n,color,p,he⟩ := hp.2.1 _ _ (hh.mp hedge)
    have he' := SubdividedWiggle.map_sameEdge (SourceMarkedProduct.cubeEncode I.k I.h) he
    simp only [SourceMarkedProduct.cubeEncode_decode] at he'
    exact ⟨n,color,p,he'⟩
  · intro n color p n' color' p' he
    have hh := SubdividedWiggle.map_sameEdge (SourceMarkedProduct.cubeDecode I.k I.h) he
    simp only [cubeTour,SourceMarkedProduct.cubeDecode_encode] at hh
    exact hp.2.2.1 n color p n' color' p' hh
  · intro n color p
    exact (SourceMarkedProduct.cube_adjacent_iff I.k I.h _ _).mpr (hp.2.2.2 n color p)

/-- Derived actual mark count, uniform across initial parents, source
addresses, twin origins and retained H assignments. -/
def markCount (I : MersenneAACBase.Input) : Nat :=
  (2*2^(I.k+I.h+1)-4)*(2^(I.e*2^(I.k+I.h+1)-1)/(2*2^(I.k+I.h+1)))*I.B

/-- Honest common folded length, from actual chronological cardinality. -/
def totalLength (I : MersenneAACBase.Input) (t : Nat) : Nat := t*(I.E+markCount I)

theorem length_eq (I : MersenneAACBase.Input) (_ht : 0<t) (n : I.Index) :
    I.length (jR:=t) n=totalLength I t :=
  MersenneAACBase.Input.fold_length I n t

theorem totalLength_pos (I : MersenneAACBase.Input) (ht : 0<t) : 0<totalLength I t :=
  Nat.mul_pos ht (by have := I.epos; omega)

/-- The uniform tour reindexes only the proved literal numeric length. -/
noncomputable def uniformTour (n : I.Index) (color : Bool) :
    Fin (totalLength I t)→Vertex (Dimension I j) := fun p =>
  cubeTour I ht JD n color (Fin.cast (length_eq I ht n).symm p)

private theorem cast_successor {N M : Nat} (he : N=M) (hN : 0<N) (hM : 0<M) (p : Fin N) :
    Fin.cast he (successor hN p)=successor hM (Fin.cast he p) := by
  subst M
  rfl

private theorem cast_back {N M : Nat} (he : N=M) (p : Fin N) :
    Fin.cast he.symm (Fin.cast he p)=p := Fin.ext rfl

private theorem uniformTour_cast (n : I.Index) (color : Bool) (p : Fin (I.length (jR:=t) n)) :
    uniformTour I ht JD n color (Fin.cast (length_eq I ht n) p)=cubeTour I ht JD n color p := by
  dsimp only [uniformTour]
  rw [cast_back]

private theorem uniform_edge (n : I.Index) (color : Bool) (p : Fin (totalLength I t)) :
    (uniformTour I ht JD n color p,
      uniformTour I ht JD n color (successor (totalLength_pos I ht) p))=
    (cubeTour I ht JD n color (Fin.cast (length_eq I ht n).symm p),
      cubeTour I ht JD n color (successor (I.length_pos ht n) (Fin.cast (length_eq I ht n).symm p))) := by
  dsimp only [uniformTour]
  rw [cast_successor (length_eq I ht n).symm (totalLength_pos I ht) (I.length_pos ht n) p]

/-- Actual UNIFORM simple cyclic tour family partitions all cube edges. -/
theorem uniform_decomposition (h2 : 2≤t) :
    (∀n color, Function.Injective (uniformTour I ht JD n color)) ∧
    (∀x y : Vertex (Dimension I j), Adjacent x y →
      ∃n color p, SameEdge (uniformTour I ht JD n color p,
        uniformTour I ht JD n color (successor (totalLength_pos I ht) p)) (x,y)) ∧
    (∀n color p n' color' p', SameEdge
      (uniformTour I ht JD n color p,uniformTour I ht JD n color (successor (totalLength_pos I ht) p))
      (uniformTour I ht JD n' color' p',uniformTour I ht JD n' color' (successor (totalLength_pos I ht) p')) →
      n=n' ∧ color=color' ∧ p=p') ∧
    (∀n color p, Adjacent (uniformTour I ht JD n color p)
      (uniformTour I ht JD n color (successor (totalLength_pos I ht) p))) := by
  have hp := cube_decomposition I ht JD h2
  refine ⟨?_,?_,?_,?_⟩
  · intro n color p q he
    have hh := hp.1 n color he
    exact Fin.ext (congrArg (fun x : Fin (I.length (jR:=t) n) => x.val) hh)
  · intro x y hh
    obtain ⟨n,color,p,he⟩ := hp.2.1 x y hh
    refine ⟨n,color,Fin.cast (length_eq I ht n) p,?_⟩
    rw [←cast_successor (length_eq I ht n) (I.length_pos ht n) (totalLength_pos I ht) p,
      uniformTour_cast,uniformTour_cast]
    exact he
  · intro n color p n' color' p' he
    rw [uniform_edge,uniform_edge] at he
    obtain ⟨hn,hcolor,hpos⟩ := hp.2.2.1 _ _ _ _ _ _ he
    exact ⟨hn,hcolor,Fin.ext (congrArg (fun x : Fin (I.length (jR:=t) n') => x.val) hpos)⟩
  · intro n color p
    change Adjacent
      (uniformTour I ht JD n color p,uniformTour I ht JD n color (successor (totalLength_pos I ht) p)).1
      (uniformTour I ht JD n color p,uniformTour I ht JD n color (successor (totalLength_pos I ht) p)).2
    rw [uniform_edge]
    exact hp.2.2.2 n color (Fin.cast (length_eq I ht n).symm p)

end Input
#print axioms Input.host_cover
#print axioms Input.host_unique
#print axioms Input.host_partition
#print axioms Input.local_host_iff
#print axioms Input.physical_decomposition
#print axioms Input.cube_decomposition
#print axioms Input.length_eq
#print axioms Input.uniform_decomposition
end ErdePaths.MersenneGlobalFold
