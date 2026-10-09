import ErdePaths.AACFineCoarseBridge
import ErdePaths.SourceHostPartition
import ErdePaths.HamiltonCommonLast

namespace ErdePaths.SourceAACBase
open SourceClock SquareLift AACTransition AACFine AACFineClock AACMarkIntervals SubdividedWiggle
open SourceProfile HamiltonData HamiltonTower HierarchicalDecode AnchoredEmbedding

section Geometry
variable {U W : Type} {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
  {t : Fin K→Bool} (E : SourceChronologicalMarks.EulerData hK hA hB t)
  (G : ClockData U (K*A)) (H : ClockData W B)

/-- Literal physical base word in the original actual fine-Euler order. -/
def base (n : Fin (K*B*(A+1))) : U×W :=
  AACFineGeometry.physical G H (fineVertex hK hA hB E.orbit E.length n)

/-- Literal retained fine host generators transported through the actual
Hamilton cycle coordinates, without any graph-ownership premise. -/
def GridHost (x y : U×W) : Prop :=
  ∃e : FineEdge K A B, SameEdge
    (AACFineGeometry.physical G H (AACTransition.decode hK hA hB e).1,
     AACFineGeometry.physical G H (AACTransition.decode hK hA hB e).2) (x,y)

theorem physical_step (n : Fin (K*B*(A+1))) :
    SameEdge
      (AACFineGeometry.physical G H (AACTransition.decode hK hA hB (fineLabel hK hA hB E.orbit E.length n)).1,
       AACFineGeometry.physical G H (AACTransition.decode hK hA hB (fineLabel hK hA hB E.orbit E.length n)).2)
      (base hK hA hB E G H n,
       base hK hA hB E G H (successor (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) n)) :=
  map_sameEdge (AACFineGeometry.physical G H)
    (fineVertex_step hK hA hB E.orbit E.length _ n)

/-- Exact physical retained-host edge coverage by consecutive base edges,
including the original numeric last-to-first seam. -/
theorem gridHost_iff (x y : U×W) : GridHost hK hA hB G H x y ↔
    ∃n : Fin (K*B*(A+1)), SameEdge
      (base hK hA hB E G H n,
       base hK hA hB E G H (successor (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) n)) (x,y) := by
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨n,hn⟩ := E.surjective e
    have hs := physical_step hK hA hB E G H n
    rw [hn] at hs
    exact ⟨n,sameEdge_trans (sameEdge_symm hs) he⟩
  · rintro ⟨n,hn⟩
    exact ⟨fineLabel hK hA hB E.orbit E.length n,
      sameEdge_trans (physical_step hK hA hB E G H n) hn⟩

/-- Actual undirected physical base-edge occurrences are unique. -/
theorem edge_unique (h3 : 3≤K*A) (hB3 : 3≤B) (n m : Fin (K*B*(A+1)))
    (he : SameEdge (base hK hA hB E G H n,
        base hK hA hB E G H (successor (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) n))
      (base hK hA hB E G H m,
        base hK hA hB E G H (successor (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) m))) : n=m := by
  exact numeric_physical_unique hK hA hB h3 hB3 E.orbit E.length _ E.injective n m
    (reflect_sameEdge (AACFineGeometry.physical G H) (AACFineGeometry.physical_injective G H) he)

/-- The physical collision law is derived for the same actual chosen orbit
and actual numeric interval colors, rather than postulated. -/
theorem color_collision (h3 : 3≤K*A) (hB3 : 3≤B) (hbeven : B%2=0)
    (hE2 : 2≤K*B*(A+1)) (z : Fin A) (hz : 0<z.val) (n m : Fin (K*B*(A+1)))
    (he : base hK hA hB E G H n=base hK hA hB E G H m) :
    n=m ∨ numericColor hK hA hB E.orbit E.length z n≠numericColor hK hA hB E.orbit E.length z m := by
  exact AACFineCoarseBridge.euler_collision hK hA hB t E h3 hB3 hbeven hE2 z hz n m
    (AACFineGeometry.physical_injective G H he)

/-- Every actual flagged mark has a unique physical base occurrence; no
mark injection or interval geometry is an input. -/
theorem mark_unique (h3 : 3≤K*A) (hB3 : 3≤B) (hbeven : B%2=0)
    (hE2 : 2≤K*B*(A+1)) (z : Fin A) (hz : 0<z.val) (n m : Fin (K*B*(A+1)))
    (hn : cyclicFlag (Nat.mul_pos (Nat.mul_pos hK hB) (by omega))
      (numericColor hK hA hB E.orbit E.length z) n=true)
    (he : base hK hA hB E G H n=base hK hA hB E G H m) : n=m := by
  have hm : n∈markPositions hK hA hB E.orbit E.length
      (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) z := by
    simpa only [markPositions,cyclicFlag,List.mem_filter,List.mem_finRange,true_and] using hn
  exact marked_collision hK hA hB h3 hB3 hbeven E.orbit E.length _ hE2 E.injective z hz n m hm
    (AACFineGeometry.physical_injective G H he)

end Geometry

section Source
variable {V W : Type} {R : V→V→Prop} {T : W→W→Prop} {m e u B b : Nat} {hB : 0<B}
  (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)
  (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
  (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
  (S : Fin m→Address a→Fin (2^(e*2^a))→Bool)
  (ho : ∀f address, Profile.cardinality (S f address)%2=1)
  (hb : ∀f, ∀address : Address (a+h), Profile.prefixCount (S f (lowerAddress address)) (2*u)=u)
  (HD : DecompositionData W T (m*(2*2^(a+h-r))) B hB) (last : W)

/-- Actual G Hamilton clock of the owned factor. -/
noncomputable def G (z : Fin (2^r)) (i : Fin (count (2*count m a) h)) :
    ClockData (VertexPower (VertexPower V a×VertexPower V a) h) (2^(e*2^(a+h+1)-r)*2^r) :=
  ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).toClockData

/-- Actual canonically assigned H clock, with its physical omission derived
by the genuine common-last normalization. -/
noncomputable def H (i : Fin (count (2*count m a) h)) : ClockData W B :=
  ((HamiltonCommonLast.normalize HD last).cycles (SourceHostPartition.association a h r hr i)).toClockData

/-- The exact literal geometric host is the already proved actual source
host, with actual normalized H factors and actual canonical association. -/
theorem gridHost_source (z : Fin (2^r)) (i : Fin (count (2*count m a) h))
    (x y : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    GridHost (Nat.two_pow_pos (e*2^(a+h+1)-r)) (Nat.two_pow_pos r) hB
      (G D he a h r hr hh room hA S ho hb z i) (H a h r hr HD last i) x y ↔
    SourceHostPartition.Host D he a h r hr hh room hA S ho hb
      (HamiltonCommonLast.normalize HD last) z i x y := by
  rw [SourceHostPartition.host_generators_iff]
  constructor
  · rintro ⟨label,hl⟩
    cases label with
    | inl p => exact Or.inl ⟨p.1,p.2,hl⟩
    | inr p => exact Or.inr ⟨p.1,p.2,hl⟩
  · rintro (⟨t,j,ht⟩ | ⟨k,j,hj⟩)
    · exact ⟨.inl (t,j),ht⟩
    · exact ⟨.inr (k,j),hj⟩

/-- Actual unrotated physical AAC Euler word, constructed uniformly. -/
noncomputable def sourceBase (z : Fin (2^r)) (i : Fin (count (2*count m a) h))
    (n : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1))) :
    VertexPower (VertexPower V a×VertexPower V a) h×W :=
  base (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB)
    (G D he a h r hr hh room hA S ho hb z i) (H a h r hr HD last i) n

/-- Derived actual source-host iff its literal successive physical AAC base
edge ledger, with no supplied host coverage or traversal existence. -/
theorem source_host_iff (z : Fin (2^r)) (i : Fin (count (2*count m a) h))
    (x y : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    SourceHostPartition.Host D he a h r hr hh room hA S ho hb
      (HamiltonCommonLast.normalize HD last) z i x y ↔
    ∃n : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1)), SameEdge
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n,
       sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n)) (x,y) := by
  rw [←gridHost_source D he a h r hr hh room hA S ho hb HD last z i]
  exact gridHost_iff (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB) _ _ x y

include he hr hB in
private theorem source_sizes :
    3≤2^(e*2^(a+h+1)-r)*2^r ∧ 2≤2^(e*2^(a+h+1)-r)*B*(2^r+1) := by
  have hk4 := SourceLengths.coarse_size he a h r hr
  have haPos := Nat.two_pow_pos r
  have hm := Nat.mul_le_mul_left (2^(e*2^(a+h+1)-r))
    (show 1≤2^r from Nat.two_pow_pos r)
  have hb1 : 1≤B := hB
  have hmB := Nat.mul_le_mul_left (2^(e*2^(a+h+1)-r)) hb1
  have hmE := Nat.mul_le_mul_left (2^(e*2^(a+h+1)-r)*B) (show 1≤2^r+1 by omega)
  simp only [Nat.mul_one] at hm hmB hmE
  omega

/-- Concrete source base edges are genuine edges of their exact owned host. -/
theorem source_adjacent (z : Fin (2^r)) (i : Fin (count (2*count m a) h))
    (n : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1))) :
    SourceHostPartition.Host D he a h r hr hh room hA S ho hb
      (HamiltonCommonLast.normalize HD last) z i
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n)
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i
        (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n)) :=
  (source_host_iff (b:=b) D he a h r hr hh room hA S ho hb HD last z i _ _).mpr ⟨n,Or.inl rfl⟩

/-- Actual source specialization: size bounds are derived, not supplied. -/
theorem source_edge_unique (hB3 : 3≤B) (z : Fin (2^r)) (i : Fin (count (2*count m a) h))
    (n n' : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1)))
    (heq : SameEdge
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n,
       sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n))
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n',
       sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n'))) : n=n' :=
  edge_unique (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB) _ _
    (source_sizes (hB:=hB) he a h r hr).1 hB3 n n' heq

/-- Literal interval color of the actual original source Euler word. -/
noncomputable def sourceColor (z : Fin (2^r)) (n : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1))) : Bool :=
  numericColor (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB).orbit
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB).length z n

theorem source_collision (hB3 : 3≤B) (hbeven : B%2=0) (z : Fin (2^r)) (hz : 0<z.val)
    (i : Fin (count (2*count m a) h)) (n n' : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1)))
    (heq : sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n=
      sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n') :
    n=n' ∨ sourceColor (b:=b) (hB:=hB) he a h r hr z n≠sourceColor (b:=b) (hB:=hB) he a h r hr z n' :=
  color_collision (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB) _ _
    (source_sizes (hB:=hB) he a h r hr).1 hB3 hbeven (source_sizes (hB:=hB) he a h r hr).2 z hz n n' heq

theorem source_mark_unique (hB3 : 3≤B) (hbeven : B%2=0) (z : Fin (2^r)) (hz : 0<z.val)
    (i : Fin (count (2*count m a) h)) (n n' : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1)))
    (hn : cyclicFlag (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega))
      (sourceColor (b:=b) (hB:=hB) he a h r hr z) n=true)
    (heq : sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n=
      sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n') : n=n' :=
  mark_unique (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB) _ _
    (source_sizes (hB:=hB) he a h r hr).1 hB3 hbeven (source_sizes (hB:=hB) he a h r hr).2 z hz n n' hn heq

/-- Actual full Cartesian edge cover through the literal global base words. -/
theorem source_product_iff (z : Fin (2^r)) (x y : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    ProductRelation (relation (ProductAdjacent (relation R a)) h) T x y ↔
    ∃i : Fin (count (2*count m a) h), ∃n : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1)), SameEdge
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n,
       sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n)) (x,y) := by
  constructor
  · intro hedge
    obtain ⟨i,hi⟩ := SourceHostPartition.host_cover D he a h r hr hh room hA S ho hb
      (HamiltonCommonLast.normalize HD last) z hedge
    obtain ⟨n,hn⟩ := (source_host_iff (b:=b) D he a h r hr hh room hA S ho hb HD last z i x y).mp hi
    exact ⟨i,n,hn⟩
  · rintro ⟨i,n,hn⟩
    exact SourceHostPartition.host_subset D he a h r hr hh room hA S ho hb
      (HamiltonCommonLast.normalize HD last) z
      ((source_host_iff (b:=b) D he a h r hr hh room hA S ho hb HD last z i x y).mpr ⟨n,hn⟩)

/-- Both global factor and actual numeric edge occurrence are unique. -/
theorem source_product_unique (hB3 : 3≤B) (z : Fin (2^r))
    (i i' : Fin (count (2*count m a) h)) (n n' : Fin (2^(e*2^(a+h+1)-r)*B*(2^r+1)))
    (heq : SameEdge
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i n,
       sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n))
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i' n',
       sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i'
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n'))) : i=i' ∧ n=n' := by
  have hi := source_adjacent (b:=b) D he a h r hr hh room hA S ho hb HD last z i n
  have hi' := (source_host_iff (b:=b) D he a h r hr hh room hA S ho hb HD last z i' _ _).mpr
    ⟨n',sameEdge_symm heq⟩
  have hii := SourceHostPartition.host_unique D he a h r hr hh room hA S ho hb
    (HamiltonCommonLast.normalize HD last) z hi hi'
  refine ⟨hii,?_⟩
  subst i'
  exact source_edge_unique (b:=b) D he a h r hr hh room hA S ho hb HD last hB3 z i n n' heq

/-- Original ordered physical mark list of the actual base, before cutting. -/
noncomputable def sourceWord (z : Fin (2^r)) (i : Fin (count (2*count m a) h)) :
    List (VertexPower (VertexPower V a×VertexPower V a) h×W) :=
  let E := SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB
  (markPositions (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) z).map
      (sourceBase (b:=b) D he a h r hr hh room hA S ho hb HD last z i)

/-- Exact original chronological word lookup, retaining each actual source
factor and its canonical H assignment; no mark-order equality is assumed. -/
theorem source_word_lookup (z : Fin (2^r)) (f : Fin m) (q : Fin (2^(a+h+1))) :
    sourceWord (b:=b) D he a h r hr hh room hA S ho hb HD last z
      (SourceFactors.index a h f (DenseSourceCounts.epsilonOf r q) (DenseSourceCounts.addressOf r q))=
    SourceChronologicalMarks.word (b:=b) he (D.cycles f).toClockData a h r hr hh room hA
      (S f) (ho f) (hb f) z hB
      (fun eps address=>((HamiltonCommonLast.normalize HD last).cycles
        (SourceHostPartition.association a h r hr (SourceFactors.index a h f eps address))).toClockData) q := by
  unfold sourceWord SourceChronologicalMarks.word markWord
  dsimp only
  rw [List.map_map]
  congr 1
  funext n
  unfold sourceBase base G H
  rw [SourceOrientedFactors.clock_eq D he a h r hr hh room hA S ho hb z]
  rfl

end Source
#print axioms source_word_lookup
#print axioms source_product_iff
#print axioms source_product_unique
#print axioms source_collision
#print axioms source_mark_unique
#print axioms source_host_iff
#print axioms edge_unique
#print axioms color_collision
#print axioms mark_unique
end ErdePaths.SourceAACBase
