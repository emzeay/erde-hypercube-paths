import ErdePaths.SourceGlobalMarks
import ErdePaths.SourceAACBase
import ErdePaths.CubePairedPartition

namespace ErdePaths.SourceMarkedProduct
open SquareLift SourceClock SourceProfile HierarchicalDecode HamiltonTower
attribute [local instance] Classical.propDecidable

section Palette
variable {V : Type} [DecidableEq V] {χ : V→Bool} {n b : Nat}
  (M : ChordGraph.Marks V χ n b) (D : MarkSchedule.Data M)

abbrev Occurrence := (i : Fin n) × Fin (M.word i).length

def occurrences : List (Occurrence M) :=
  (List.finRange n).flatMap fun i => (List.finRange (M.word i).length).map fun o => ⟨i,o⟩

theorem occurrence_mem (o : Occurrence M) : o∈occurrences M :=
  List.mem_flatMap.mpr ⟨o.1,List.mem_finRange _,List.mem_map.mpr ⟨o.2,List.mem_finRange _,rfl⟩⟩

/-- The actual proved palette gives a unique original chronological
occurrence at each physical vertex and each physical cycle color. -/
theorem palette_owner (v : V) (c : Fin b) :
    ∃o : Occurrence M, (M.word o.1)[o.2]=v ∧ D.labels o.1 o.2=c ∧
      ∀p : Occurrence M, (M.word p.1)[p.2]=v → D.labels p.1 p.2=c → p=o := by
  let P := fun o : Occurrence M => decide ((M.word o.1)[o.2]=v ∧ D.labels o.1 o.2=c)
  have hc : (occurrences M).countP P=1 := by
    unfold occurrences
    rw [List.countP_flatMap]
    simp only [List.countP_map,Function.comp_def]
    exact D.palette v c
  rw [List.countP_eq_length_filter] at hc
  obtain ⟨o,ho⟩ := List.length_eq_one_iff.mp hc
  have hm : o∈(occurrences M).filter P := by rw [ho]; simp
  have hp := (List.mem_filter.mp hm).2
  have hh : (M.word o.1)[o.2]=v ∧ D.labels o.1 o.2=c := by
    simpa only [P,decide_eq_true_eq] using hp
  refine ⟨o,hh.1,hh.2,?_⟩
  intro p hv hl
  have hm : p∈(occurrences M).filter P :=
    List.mem_filter.mpr ⟨occurrence_mem M p,by simp only [P,decide_eq_true_eq]; exact ⟨hv,hl⟩⟩
  rw [ho] at hm
  exact List.mem_singleton.mp hm

/-- Actual marked input host of one original word; its vertical cycle is
chosen by the exact palette label at that literal mark occurrence. -/
def MarkedHost {X : Type} {R : X→X→Prop} {ξ : X→Bool} {t : Nat} {ht : 0<t}
    (base : Fin n→V→V→Prop) (cycles : Fin b→PairedLayers.CycleData X R ξ t ht)
    (i : Fin n) (x y : V×X) : Prop :=
  (x.2=y.2 ∧ base i x.1 y.1) ∨
    (x.1=y.1 ∧ ∃o : Fin (M.word i).length,
      (M.word i)[o]=x.1 ∧ AACFoldEdgeLedger.CycleAdjacent (cycles (D.labels i o)) x.2 y.2)

end Palette

section Actual
variable {e d j m u B b t : Nat}
variable (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
variable (he : 2≤e) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
variable (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
variable (S : Fin m→Address a→Fin (2^(e*2^a))→Bool)
variable (ho : ∀f address, Profile.cardinality (S f address)%2=1)
variable (hb : ∀f, ∀address : Address (a+h), Profile.prefixCount (S f (lowerAddress address)) (2*u)=u)
variable (z : Fin (2^r)) (hz : 0<z.val)
variable (hB : 0<B) (hB4 : 4≤B) (hbeven : B%2=0)
variable (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) (m*(2*2^(a+h-r))) B hB)
variable (last : Vertex d) (hbnd : b<2^(a+h+1-r)) (hodd : b%2=1)
variable (ht : 0<t)
variable (JD : HamiltonData.DecompositionData (Vertex j) (@Adjacent j) (m*b) (2*t) (by omega))

/-- Canonical retained H assignment, with actual SourceFactors identity. -/
noncomputable def assigned (f : Fin m) (eps : Bool) (address : Address (a+h)) : Fin (m*(2*2^(a+h-r))) :=
  SourceHostPartition.association a h r hr (SourceFactors.index a h f eps address)

noncomputable def marks := SourceGlobalMarks.marks D he a h r hr hh room hA S ho hb z hz
  hB hB4 hbeven HD last (assigned a h r hr) hbnd hodd

noncomputable def schedule := SourceGlobalMarks.schedule D he a h r hr hh room hA S ho hb z hz
  hB hB4 hbeven HD last (assigned a h r hr) hbnd hodd

noncomputable def baseHost (i : Fin (m*2^(a+h+1)))
    (x y : SourceGlobalMarks.Physical e d a h) : Prop :=
  SourceHostPartition.Host D he a h r hr hh room hA S ho hb
    (HamiltonCommonLast.normalize HD last) z (SourceGlobalMarks.sourceIndex a h r i) x y

noncomputable def Host (i : Fin (m*2^(a+h+1)))
    (x y : SourceGlobalMarks.Physical e d a h × Vertex j) : Prop :=
  MarkedHost (marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd)
    (schedule D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd)
    (baseHost D he a h r hr hh room hA S ho hb z hB HD last) (CubePairedPartition.cycles ht JD) i x y

def BaseRelation : SourceGlobalMarks.Physical e d a h→SourceGlobalMarks.Physical e d a h→Prop :=
  AnchoredEmbedding.ProductRelation
    (HamiltonTower.relation (ProductAdjacent (HamiltonTower.relation (@Adjacent e) a)) h) (@Adjacent d)


/-- Actual canonical global word equals the marked word of its actual
owned SourceAACBase host; no mark-order equivalence is supplied. -/
theorem word_base (i : Fin (m*2^(a+h+1))) :
    (marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd).word i=
      SourceAACBase.sourceWord (b:=b) D he a h r hr hh room hA S ho hb HD last z
        (SourceGlobalMarks.sourceIndex a h r i) := by
  let p := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (a+h+1)) i
  have hi : AnchoredEmbedding.positionEncode p.1 p.2=i := AnchoredEmbedding.positionEncode_decode _ i
  rw [←hi]
  unfold marks
  rw [SourceGlobalMarks.word_lookup,SourceGlobalMarks.sourceIndex_lookup,
    SourceAACBase.source_word_lookup]
  rfl

/-- Genuine base-host ownership is inherited from the actual canonical
source association and actual normalized H factorization. -/
theorem base_cover {x y : SourceGlobalMarks.Physical e d a h}
    (hedge : BaseRelation (e:=e) (d:=d) (a:=a) (h:=h) x y) :
    ∃i, baseHost D he a h r hr hh room hA S ho hb z hB HD last i x y := by
  obtain ⟨q,hq⟩ := SourceHostPartition.host_cover D he a h r hr hh room hA S ho hb
    (HamiltonCommonLast.normalize HD last) z hedge
  obtain ⟨i,hi⟩ := SourceGlobalMarks.sourceIndex_surjective (m:=m) a h r hr q
  refine ⟨i,?_⟩
  unfold baseHost
  rw [hi]
  exact hq

theorem base_relation {i : Fin (m*2^(a+h+1))} {x y : SourceGlobalMarks.Physical e d a h}
    (hi : baseHost D he a h r hr hh room hA S ho hb z hB HD last i x y) :
    BaseRelation (e:=e) (d:=d) (a:=a) (h:=h) x y :=
  SourceHostPartition.host_subset D he a h r hr hh room hA S ho hb
    (HamiltonCommonLast.normalize HD last) z hi

theorem base_unique {i i' : Fin (m*2^(a+h+1))} {x y : SourceGlobalMarks.Physical e d a h}
    (hi : baseHost D he a h r hr hh room hA S ho hb z hB HD last i x y)
    (hi' : baseHost D he a h r hr hh room hA S ho hb z hB HD last i' x y) : i=i' :=
  SourceGlobalMarks.sourceIndex_injective a h r hr
    (SourceHostPartition.host_unique D he a h r hr hh room hA S ho hb
      (HamiltonCommonLast.normalize HD last) z hi hi')

private theorem base_loopfree (v : SourceGlobalMarks.Physical e d a h) :
    ¬BaseRelation (e:=e) (d:=d) (a:=a) (h:=h) v v := by
  rintro (⟨_,hg⟩ | ⟨_,hh'⟩)
  · exact adjacent_ne ((CubeHierarchy.sourceIso e a h).adjacent v.1 v.1 |>.mpr hg) rfl
  · exact adjacent_ne hh' rfl

/-- Every actual marked-host edge belongs to the genuine nested product. -/
theorem host_relation {i : Fin (m*2^(a+h+1))}
    {x y : SourceGlobalMarks.Physical e d a h × Vertex j}
    (hi : Host D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD i x y) :
    AnchoredEmbedding.ProductRelation (BaseRelation (e:=e) (d:=d) (a:=a) (h:=h)) (@Adjacent j) x y := by
  rcases hi with ⟨hj,hbase⟩ | ⟨hv,o,ho,hcycle⟩
  · exact Or.inl ⟨hj,base_relation D he a h r hr hh room hA S ho hb z hB HD last hbase⟩
  · exact Or.inr ⟨hv,CubePairedPartition.relation ht JD hcycle⟩

/-- Every genuine product edge has an actual marked host owner. Vertical
ownership is obtained from the PROVED actual global palette. -/
theorem host_cover {x y : SourceGlobalMarks.Physical e d a h × Vertex j}
    (hedge : AnchoredEmbedding.ProductRelation (BaseRelation (e:=e) (d:=d) (a:=a) (h:=h)) (@Adjacent j) x y) :
    ∃i, Host D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD i x y := by
  rcases hedge with ⟨hj,hbase⟩ | ⟨hv,hj⟩
  · obtain ⟨i,hi⟩ := base_cover D he a h r hr hh room hA S ho hb z hB HD last hbase
    exact ⟨i,Or.inl ⟨hj,hi⟩⟩
  · obtain ⟨c,hc⟩ := CubePairedPartition.cover ht JD x.2 y.2 hj
    obtain ⟨o,ho,hl,_⟩ := palette_owner
      (marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd)
      (schedule D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd) x.1 c
    refine ⟨o.1,Or.inr ⟨hv,o.2,ho,?_⟩⟩
    rw [hl]
    exact hc

/-- Actual vertical mark occurrences are unique, even across different
base source hosts and different actual H assignments. -/
theorem vertical_occurrence_unique (v : SourceGlobalMarks.Physical e d a h) (x y : Vertex j)
    (i i' : Fin (m*2^(a+h+1)))
    (o : Fin ((marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd).word i).length)
    (o' : Fin ((marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd).word i').length)
    (hv : ((marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd).word i)[o]=v)
    (hv' : ((marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd).word i')[o']=v)
    (hj : AACFoldEdgeLedger.CycleAdjacent (CubePairedPartition.cycles ht JD
      ((schedule D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd).labels i o)) x y)
    (hj' : AACFoldEdgeLedger.CycleAdjacent (CubePairedPartition.cycles ht JD
      ((schedule D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd).labels i' o')) x y) :
    (⟨i,o⟩ : Occurrence (marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd))=⟨i',o'⟩ := by
  have hc := CubePairedPartition.unique ht JD hj hj'
  obtain ⟨owner,_,_,hu⟩ := palette_owner
    (marks D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd)
    (schedule D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd) v
    ((schedule D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd).labels i o)
  exact (hu ⟨i,o⟩ hv rfl).trans (hu ⟨i',o'⟩ hv' hc.symm).symm

/-- No global marked host shares a physical product edge with another. -/
theorem host_unique {i i' : Fin (m*2^(a+h+1))}
    {x y : SourceGlobalMarks.Physical e d a h × Vertex j}
    (hi : Host D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD i x y)
    (hi' : Host D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD i' x y) : i=i' := by
  rcases hi with ⟨hx,hb1⟩ | ⟨hv,o,hmarkleft,hj⟩
  · rcases hi' with ⟨_,hb2⟩ | ⟨hv,_,_,_⟩
    · exact base_unique D he a h r hr hh room hA S ho hb z hB HD last hb1 hb2
    · have hh' := base_relation D he a h r hr hh room hA S ho hb z hB HD last hb1
      rw [hv] at hh'
      exact False.elim (base_loopfree a h _ hh')
  · rcases hi' with ⟨_,hb2⟩ | ⟨_,o',ho',hj'⟩
    · have hh' := base_relation D he a h r hr hh room hA S ho hb z hB HD last hb2
      rw [hv] at hh'
      exact False.elim (base_loopfree a h _ hh')
    · exact congrArg Sigma.fst
        (vertical_occurrence_unique D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD
          x.1 x.2 y.2 i i' o o' hmarkleft ho' hj hj')

/-- Full actual marked input-host partition. All base-host ownership and
physical mark palette facts are derived by its constructors. -/
theorem host_partition (x y : SourceGlobalMarks.Physical e d a h × Vertex j) :
    AnchoredEmbedding.ProductRelation (BaseRelation (e:=e) (d:=d) (a:=a) (h:=h)) (@Adjacent j) x y ↔
    ∃i, Host D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD i x y ∧
      ∀i', Host D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD i' x y→i'=i := by
  constructor
  · intro hedge
    obtain ⟨i,hi⟩ := host_cover D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD hedge
    exact ⟨i,hi,fun i' hi' => host_unique D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD hi' hi⟩
  · rintro ⟨i,hi,_⟩
    exact host_relation D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD hi

/-- Exact actual binary base-host relation, through the existing hierarchy
coordinate maps; no graph isomorphism is postulated. -/
theorem base_cube_iff (x y : SourceGlobalMarks.Physical e d a h) :
    Adjacent (SourceGlobalMarks.encode x) (SourceGlobalMarks.encode y) ↔
      BaseRelation (e:=e) (d:=d) (a:=a) (h:=h) x y := by
  unfold SourceGlobalMarks.encode
  rw [CubeProduct.adjacent_iff]
  constructor
  · rintro (⟨hw,hg⟩ | ⟨hg,hw⟩)
    · exact Or.inl ⟨hw,((CubeHierarchy.sourceIso e a h).adjacent _ _).mp hg⟩
    · exact Or.inr ⟨CubeHierarchy.encode_injective _ hg,hw⟩
  · rintro (⟨hw,hg⟩ | ⟨hg,hw⟩)
    · exact Or.inl ⟨hw,((CubeHierarchy.sourceIso e a h).adjacent _ _).mpr hg⟩
    · exact Or.inr ⟨congrArg (CubeHierarchy.sourceIso e a h).encode hg,hw⟩

def cubeEncode (v : SourceGlobalMarks.Physical e d a h × Vertex j) :
    Vertex (e*2^(a+h+1)+d+j) := CubeProduct.encode (SourceGlobalMarks.encode v.1,v.2)

def cubeDecode (v : Vertex (e*2^(a+h+1)+d+j)) :
    SourceGlobalMarks.Physical e d a h × Vertex j :=
  (SourceGlobalMarks.decode (CubeProduct.decode v).1,(CubeProduct.decode v).2)

theorem cubeDecode_encode (v : SourceGlobalMarks.Physical e d a h × Vertex j) :
    cubeDecode a h (cubeEncode a h v)=v := by
  simp only [cubeEncode,cubeDecode,CubeProduct.decode_encode,SourceGlobalMarks.decode_encode]

theorem cubeEncode_decode (v : Vertex (e*2^(a+h+1)+d+j)) :
    cubeEncode a h (cubeDecode a h v)=v := by
  simp only [cubeEncode,cubeDecode,SourceGlobalMarks.encode_decode]
  exact CubeProduct.encode_decode v

theorem cube_adjacent_iff (x y : SourceGlobalMarks.Physical e d a h × Vertex j) :
    Adjacent (cubeEncode a h x) (cubeEncode a h y) ↔
      AnchoredEmbedding.ProductRelation (BaseRelation (e:=e) (d:=d) (a:=a) (h:=h)) (@Adjacent j) x y := by
  unfold cubeEncode
  rw [CubeProduct.adjacent_iff]
  constructor
  · rintro (⟨hj,hbase⟩ | ⟨hbase,hj⟩)
    · exact Or.inl ⟨hj,(base_cube_iff a h _ _).mp hbase⟩
    · have hh := congrArg SourceGlobalMarks.decode hbase
      simp only [SourceGlobalMarks.decode_encode] at hh
      exact Or.inr ⟨hh,hj⟩
  · rintro (⟨hj,hbase⟩ | ⟨hbase,hj⟩)
    · exact Or.inl ⟨hj,(base_cube_iff a h _ _).mpr hbase⟩
    · exact Or.inr ⟨congrArg SourceGlobalMarks.encode hbase,hj⟩

/-- Genuine binary-cube edge partition into these actual marked hosts. The
only Hamilton partition inputs are the original D, retained HD, and JD. -/
theorem cube_host_partition (x y : Vertex (e*2^(a+h+1)+d+j)) :
    Adjacent x y ↔
    ∃i, Host D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD i
      (cubeDecode a h x) (cubeDecode a h y) ∧
      ∀i', Host D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD i'
        (cubeDecode a h x) (cubeDecode a h y)→i'=i := by
  have hi := cube_adjacent_iff a h (cubeDecode a h x) (cubeDecode a h y)
  rw [cubeEncode_decode,cubeEncode_decode] at hi
  exact hi.trans (host_partition D he a h r hr hh room hA S ho hb z hz hB hB4 hbeven HD last hbnd hodd ht JD _ _)

end Actual
#print axioms palette_owner
#print axioms word_base
#print axioms vertical_occurrence_unique
#print axioms host_partition
#print axioms cube_host_partition
end ErdePaths.SourceMarkedProduct
