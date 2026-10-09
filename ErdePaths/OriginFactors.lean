import ErdePaths.QuarterSourceOrigins
import ErdePaths.SourceHostPartition

namespace ErdePaths.OriginFactors
open SourceClock SourceProfile HamiltonData HamiltonTower HierarchicalDecode SquareLift
open OrientedClock AACResidueBridge SourceStability SourceAnchorGroups

/-- Canonical fixed-twin/high-address H assignment, reserved slot one. -/
noncomputable def association {m : Nat} (k h : Nat) (hk : 1<k+h+1)
    (q : Fin (count (2*count m k) h)) : Fin (m*(2*2^(k+h-1))) :=
  SourceHostPartition.association k h 1 (by omega) q

/-- Actual oriented source clock from genuine same-endpoint profile arcs.
This definition permits zero upper depth and requires no prefix-balance
premise: the actual arc Data records the concrete endpoint codes. -/
noncomputable def orientedSource {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 1<k+h+1)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
      (origins : ∀a : Address (k+h), SourceCodeOrigins.Data (u:=1) he C k h 1 (by omega) S ho a)
    (epsilon : Bool) (a : Address (k+h)) (z : Fin 2) :
    ClockData (VertexPower (VertexPower V k×VertexPower V k) h)
      (2^(e*2^(k+h+1)-1)*2) :=
  let data:=origins a
  let raw:=castClock (SourceLengths.fine_length he k h 1 (by omega))
    (SourceProfile.clock he C k h S ho epsilon a)
  let ep:=Fin.cast (SourceLengths.fine_length he k h 1 (by omega)) (SourceCodeOrigins.endpoint data epsilon)
  let hK:=Nat.two_pow_pos (e*2^(k+h+1)-1)
  OrientedClock.clock (Nat.mul_pos hK (by decide)) raw
    (OrientedClock.index (Nat.mul_pos hK (by decide)) ep (!epsilon) (BaselinePhysical.threshold hK z)) epsilon

section Coordinates
variable {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k h : Nat) (hk : 1<k+h+1)
  (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
  (origins : ∀address : Address (k+h), SourceCodeOrigins.Data (u:=1) he C k h 1 (by omega) S ho address)

/-- Actual source old-grid ownership uses only its proved low source bit;
no injectivity of the full occurrence code is required. -/
theorem anchor_iff (epsilon : Bool) (address : Address (k+h)) (z : Fin 2)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ((orientedSource he C k h hk S ho origins epsilon address z).position v).val%2=0 ↔
    SourceAnchorGroups.Owns he C k h 1 (by omega) S ho epsilon v
      (signedOffset (2^(k+h+1)) 1 z.val epsilon) address := by
  let data := origins address
  let raw := castClock (SourceLengths.fine_length he k h 1 (by omega)) (SourceProfile.clock he C k h S ho epsilon address)
  let ep := Fin.cast (SourceLengths.fine_length he k h 1 (by omega)) (SourceCodeOrigins.endpoint data epsilon)
  have hsmall : 2∣2^(k+h+1) := Nat.pow_dvd_pow 2 (show 1≤k+h+1 by omega)
  have hcode : (SourceCodeOrigins.endpoint data epsilon).val%2=
      (DenseSourceMarks.code 1 (by omega) epsilon address).val%2 := by
    have hc := congrArg (fun n=>n%2) (SourceCodeOrigins.endpoint_code data epsilon)
    rw [Nat.mod_mod_of_dvd _ hsmall] at hc
    exact hc
  have hg := SourceAnchorCoordinates.grid_residue_iff
    (Nat.mul_pos (Nat.two_pow_pos (e*2^(k+h+1)-1)) (by decide : 0<2))
    (by decide : 0<2) (Nat.dvd_mul_left 2 _) raw ep
    (BaselinePhysical.threshold (Nat.two_pow_pos _) z) epsilon v
  change _ ↔ SourceAnchorGroups.Owns he C k h 1 (by omega) S ho epsilon v _ address
  unfold SourceAnchorGroups.Owns shiftedValue
  rw [SourceAnchorCoordinates.signed_shift_reduce (Nat.two_pow_pos _) (by decide : 0<2) hsmall]
  change _ ↔ shiftedResidue 2 (signedOffset 2 1 z.val epsilon)
    ((SourceProfile.clock he C k h S ho epsilon address).position v).val=
      (DenseSourceMarks.code 1 (by omega) epsilon address).val%2
  rw [←hcode]
  simpa only [raw,ep,castClock_position,Fin.val_cast,BaselinePhysical.threshold,
    orientedSource,data] using hg

/-- Exactly one actual source coordinate-zero grid owner within each
fixed twin/high-address group, derived from the actual causal decoder. -/
theorem unique_grid_owner (epsilon : Bool) (high : Address (k+h)) (z : Fin 2)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ∃address, InGroup 1 high address ∧
      ((orientedSource he C k h hk S ho origins epsilon address z).position v).val%2=0 ∧
      ∀address', InGroup 1 high address'→
        ((orientedSource he C k h hk S ho origins epsilon address' z).position v).val%2=0→address'=address := by
  obtain ⟨address,hgroup,hown,hu⟩ := SourceAnchorGroups.unique_group_owner he C k h 1
    (by omega) S ho epsilon high v (signedOffset (2^(k+h+1)) 1 z.val epsilon)
  refine ⟨address,hgroup,(anchor_iff he C k h hk S ho origins epsilon address z v).mpr hown,?_⟩
  intro address' hgroup' hgrid'
  exact hu address' hgroup' ((anchor_iff he C k h hk S ho origins epsilon address' z v).mp hgrid')

end Coordinates

section Factors
variable {V : Type} {R : V→V→Prop} {m e : Nat}
  (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)
  (k h : Nat) (hk : 1<k+h+1)
  (S : Fin m→Address k→Fin (2^(e*2^k))→Bool)
  (ho : ∀f address, Profile.cardinality (S f address)%2=1)
  (origins : ∀f, ∀address : Address (k+h), SourceCodeOrigins.Data (u:=1) he (D.cycles f).toClockData k h 1 (by omega) (S f) (ho f) address)

noncomputable def startsFor (z : Fin 2) (cfg : Fin m×Bool×Address (k+h)) :
    Fin (2^(e*2^(k+h+1)-1)*2) :=
  let data := origins cfg.1 cfg.2.2
  OrientedClock.index (Nat.mul_pos (Nat.two_pow_pos _) (by decide : 0<2))
    (Fin.cast (SourceLengths.fine_length he k h 1 (by omega)) (SourceCodeOrigins.endpoint data cfg.2.1))
    (!cfg.2.1) (BaselinePhysical.threshold (Nat.two_pow_pos _) z)

noncomputable def starts (z : Fin 2) (q : Fin (count (2*count m k) h)) :
    Fin (2^(e*2^(k+h+1)-1)*2) :=
  startsFor D he k h hk S ho origins z (SourceOrientedFactors.configuration k h q)

/-- Genuine full Hamilton partition using the actual source occurrence
origins and twin directions. No output adjacency/partition premise. -/
noncomputable def factors (z : Fin 2) :
    DecompositionData (VertexPower (VertexPower V k×VertexPower V k) h)
      (relation (ProductAdjacent (relation R k)) h) (count (2*count m k) h)
      (2^(e*2^(k+h+1)-1)*2) (Nat.mul_pos (Nat.two_pow_pos _) (by decide : 0<2)) :=
  HamiltonOrient.factors (SourceOrientedFactors.base D he k h 1 (by omega) S ho)
    (starts D he k h hk S ho origins z) (SourceOrientedFactors.directions k h)

/-- Owned actual Hamilton factor and geometric source clock coincide. -/
theorem clock_eq (z : Fin 2) (f : Fin m) (epsilon : Bool) (address : Address (k+h)) :
    ((factors D he k h hk S ho origins z).cycles
      (SourceFactors.index k h f epsilon address)).toClockData=
      orientedSource he (D.cycles f).toClockData k h hk
        (S f) (ho f) (origins f) epsilon address z := by
  unfold factors HamiltonOrient.factors
  change OrientedClock.clock _
    (((SourceOrientedFactors.base D he k h 1 (by omega) S ho).cycles
      (SourceFactors.index k h f epsilon address)).toClockData)
    (starts D he k h hk S ho origins z (SourceFactors.index k h f epsilon address))
    (SourceOrientedFactors.directions k h (SourceFactors.index k h f epsilon address))=_
  unfold starts SourceOrientedFactors.directions
  rw [SourceOrientedFactors.index_configuration]
  unfold SourceOrientedFactors.base
  rw [SourceFactors.castDecomposition_clock,SourceFactors.clock_eq]
  rfl

/-- Every H group has an actual old-grid owner at every physical G vertex. -/
theorem representative_cover (z : Fin 2) (j : Fin (m*(2*2^(k+h-1))))
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ∃i : Fin (count (2*count m k) h), association k h hk i=j ∧
      (((factors D he k h hk S ho origins z).cycles i).position v).val%2=0 := by
  let key := SourceHostPartition.indexKey j
  obtain ⟨address,hgroup,hgrid,_⟩ := unique_grid_owner he (D.cycles key.1).toClockData
    k h hk (S key.1) (ho key.1) (origins key.1) key.2.1
    (highAddress 1 (by omega) key.2.2) z v
  refine ⟨SourceFactors.index k h key.1 key.2.1 address,?_,?_⟩
  · unfold association
    rw [SourceHostPartition.association_index,
      SourceHostPartition.highKey_eq 1 (by omega) key.2.2 address hgroup]
    exact SourceHostPartition.keyIndex_indexKey j
  · rw [←clock_eq D he k h hk S ho origins z] at hgrid
    exact hgrid

/-- Actual coordinate-zero ownership is unique within every fixed
twin/high-address group, using its genuine causal clock. -/
theorem representative_unique (z : Fin 2) (i i' : Fin (count (2*count m k) h))
    (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (hai : association k h hk i=association k h hk i')
    (hi : (((factors D he k h hk S ho origins z).cycles i).position v).val%2=0)
    (hi' : (((factors D he k h hk S ho origins z).cycles i').position v).val%2=0) : i=i' := by
  let cfg := SourceOrientedFactors.configuration k h i
  let cfg' := SourceOrientedFactors.configuration k h i'
  have hkey := SourceHostPartition.keyIndex_injective hai
  have hf : cfg.1=cfg'.1 := congrArg (fun q : SourceHostPartition.Key m (k+h) 1=>q.1) hkey
  have heps : cfg.2.1=cfg'.2.1 := congrArg (fun q : SourceHostPartition.Key m (k+h) 1=>q.2.1) hkey
  have hhigh : SourceHostPartition.highKey 1 (by omega) cfg.2.2=
      SourceHostPartition.highKey 1 (by omega) cfg'.2.2 :=
    congrArg (fun q : SourceHostPartition.Key m (k+h) 1=>q.2.2) hkey
  have hci := SourceOrientedFactors.configuration_index k h i
  have hci' := SourceOrientedFactors.configuration_index k h i'
  change SourceFactors.index k h cfg.1 cfg.2.1 cfg.2.2=i at hci
  change SourceFactors.index k h cfg'.1 cfg'.2.1 cfg'.2.2=i' at hci'
  rw [←hci,clock_eq D he k h hk S ho origins z] at hi
  rw [←hci',clock_eq D he k h hk S ho origins z,←hf,←heps] at hi'
  obtain ⟨owner,_,_,hu⟩ := unique_grid_owner he (D.cycles cfg.1).toClockData k h hk
    (S cfg.1) (ho cfg.1) (origins cfg.1) cfg.2.1
    (highAddress 1 (by omega) (SourceHostPartition.highKey 1 (by omega) cfg.2.2)) z v
  have hgroup := SourceHostPartition.highKey_group 1 (by omega) cfg.2.2
  have hgroup' := SourceHostPartition.highKey_group 1 (by omega) cfg'.2.2
  rw [←hhigh] at hgroup'
  have had := (hu cfg.2.2 hgroup hi).trans (hu cfg'.2.2 hgroup' hi').symm
  exact hci.symm.trans ((congrArg (fun address=>SourceFactors.index k h cfg.1 cfg.2.1 address) had).trans
    (by rw [hf,heps]; exact hci'))

section Host
variable {W : Type} {T : W→W→Prop} {B : Nat} {hB : 0<B}
  (H : DecompositionData W T (m*(2*2^(k+h-1))) B hB)

/-- Actual source anchored host, with the constructed assigned H factor. -/
noncomputable def Host (z : Fin 2) (i : Fin (count (2*count m k) h))
    (x y : VertexPower (VertexPower V k×VertexPower V k) h×W) : Prop :=
  (x.2=y.2 ∧ SourceHostPartition.FactorEdge (factors D he k h hk S ho origins z) i x.1 y.1) ∨
  (x.1=y.1 ∧ (((factors D he k h hk S ho origins z).cycles i).position x.1).val%2=0 ∧
    SourceHostPartition.FactorEdge H (association k h hk i) x.2 y.2)

theorem host_subset (z : Fin 2) {i : Fin (count (2*count m k) h)}
    {x y : VertexPower (VertexPower V k×VertexPower V k) h×W}
    (hi : Host D he k h hk S ho origins H z i x y) :
    AnchoredEmbedding.ProductRelation (relation (ProductAdjacent (relation R k)) h) T x y := by
  rcases hi with ⟨hw,hi⟩ | ⟨hv,_,hi⟩
  · exact Or.inl ⟨hw,SourceHostPartition.factorEdge_relation _ hi⟩
  · exact Or.inr ⟨hv,SourceHostPartition.factorEdge_relation _ hi⟩

theorem host_cover (z : Fin 2) {x y : VertexPower (VertexPower V k×VertexPower V k) h×W}
    (hedge : AnchoredEmbedding.ProductRelation (relation (ProductAdjacent (relation R k)) h) T x y) :
    ∃i : Fin (count (2*count m k) h), Host D he k h hk S ho origins H z i x y := by
  rcases hedge with ⟨hw,hedge⟩ | ⟨hv,hedge⟩
  · obtain ⟨i,t,ht⟩ := (factors D he k h hk S ho origins z).cover x.1 y.1 hedge
    exact ⟨i,Or.inl ⟨hw,t,ht⟩⟩
  · obtain ⟨j,t,ht⟩ := H.cover x.2 y.2 hedge
    obtain ⟨i,hai,hgrid⟩ := representative_cover D he k h hk S ho origins z j x.1
    exact ⟨i,Or.inr ⟨hv,hgrid,by rw [hai]; exact ⟨t,ht⟩⟩⟩

theorem host_unique (z : Fin 2) {i i' : Fin (count (2*count m k) h)}
    {x y : VertexPower (VertexPower V k×VertexPower V k) h×W}
    (hi : Host D he k h hk S ho origins H z i x y)
    (hi' : Host D he k h hk S ho origins H z i' x y) : i=i' := by
  rcases hi with ⟨hw,hi⟩ | ⟨hv,hgi,hi⟩
  · rcases hi' with ⟨_,hi'⟩ | ⟨hv,_,_⟩
    · exact SourceHostPartition.factorEdge_unique _ hi hi'
    · have hg := SourceHostPartition.factorEdge_relation _ hi
      rw [hv] at hg
      exact False.elim ((factors D he k h hk S ho origins z).loopfree _ hg)
  · rcases hi' with ⟨_,hi'⟩ | ⟨_,hgi',hi'⟩
    · have hg := SourceHostPartition.factorEdge_relation _ hi'
      rw [hv] at hg
      exact False.elim ((factors D he k h hk S ho origins z).loopfree _ hg)
    · exact representative_unique D he k h hk S ho origins z i i' x.1
        (SourceHostPartition.factorEdge_unique H hi hi') hgi hgi'

theorem host_partition (z : Fin 2) (x y : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    AnchoredEmbedding.ProductRelation (relation (ProductAdjacent (relation R k)) h) T x y ↔
    ∃i : Fin (count (2*count m k) h), Host D he k h hk S ho origins H z i x y ∧
      ∀i', Host D he k h hk S ho origins H z i' x y→i'=i := by
  constructor
  · intro hedge
    obtain ⟨i,hi⟩ := host_cover D he k h hk S ho origins H z hedge
    exact ⟨i,hi,fun _ hi'=>host_unique D he k h hk S ho origins H z hi' hi⟩
  · rintro ⟨_,hi,_⟩
    exact host_subset D he k h hk S ho origins H z hi
end Host

end Factors

namespace Quarter
variable {V : Type} {R : V→V→Prop} {m e : Nat}
  (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)

/-- Genuine shifted-profile Hamilton factors with literal zero-upper-depth
origins internally constructed for every source parent. -/
noncomputable def factors (z : Fin 2) :
    DecompositionData (VertexPower V 1×VertexPower V 1)
      (ProductAdjacent (relation R 1)) (2*count m 1)
      (2^(e*2^(1+0+1)-1)*2) (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) :=
  OriginFactors.factors D he 1 0 (by decide)
    (fun _=>QuarterProfileOrigins.selectors he) (fun _=>QuarterProfileOrigins.odd he)
    (fun f=>QuarterSourceOrigins.data he (D.cycles f).toClockData) z

end Quarter
#print axioms host_partition
#print axioms Quarter.factors
end ErdePaths.OriginFactors
