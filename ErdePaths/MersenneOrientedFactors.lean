import ErdePaths.MersennePhysicalIncidence
import ErdePaths.SourceHostPartition

namespace ErdePaths.MersenneOrientedFactors
open SourceClock SourceProfile HamiltonData HamiltonTower HierarchicalDecode SquareLift
open OrientedClock AACResidueBridge SourceStability SourceAnchorGroups

/-- Mersenne full codes can repeat; their low bit nevertheless equals the
literal source bit, exactly as the dense reserved-one code. -/
theorem code_mod_two {K : Nat} (hk : 2≤K) (exceptional epsilon : Bool) (address : Address K) :
    (MersenneCode.code hk exceptional epsilon address).val%2=
      (DenseSourceMarks.code 1 (by omega) epsilon address).val%2 := by
  have hm := congrFun (MersenneCode.code_bits hk exceptional epsilon address) ⟨0,by omega⟩
  have hd := DenseSourceMarks.code_source 1 (by omega) epsilon address ⟨0,by omega⟩
  simp only [binaryTuple,MersenneCode.codeBits,↓reduceIte] at hm
  simp only [sparsePosition,show 0<1 from by decide,ite_true] at hd
  have hb := hm.trans hd.symm
  simp only [Nat.testBit_zero,decide_eq_decide] at hb
  have hml := Nat.mod_lt (MersenneCode.code hk exceptional epsilon address).val (by decide : 0<2)
  have hdl := Nat.mod_lt (DenseSourceMarks.code 1 (by omega) epsilon address).val (by decide : 0<2)
  omega

/-- Canonical fixed-twin/high-address H assignment, reserved slot one. -/
noncomputable def association {m : Nat} (k h : Nat) (hk : 2≤k)
    (q : Fin (count (2*count m k) h)) : Fin (m*(2*2^(k+h-1))) :=
  SourceHostPartition.association k h 1 (by omega) q

section Coordinates
variable {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k h : Nat) (hk : 2≤k) (hh : 0<h)
  (room : 2^(k+h+3)∣lengthPower (2^e) k)
  (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
  (hb : ∀address : Address (k+h), Profile.prefixCount (S (lowerAddress address)) 2=1)
  (exceptional : Bool)

/-- Actual Mersenne old-grid ownership uses only its proved low source bit;
no injectivity of the exceptional full occurrence code is required. -/
theorem anchor_iff (epsilon : Bool) (address : Address (k+h)) (z : Fin 2)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ((MersennePhysicalIncidence.orientedSource he C k h hk hh room S ho hb exceptional epsilon address z).position v).val%2=0 ↔
    SourceAnchorGroups.Owns he C k h 1 (by omega) S ho epsilon v
      (signedOffset (2^(k+h+1)) 1 z.val epsilon) address := by
  let data := MersenneCodeOrigins.family he C k h (by omega) hh room S ho hb exceptional address
  let raw := castClock (SourceLengths.fine_length he k h 1 (by omega)) (SourceProfile.clock he C k h S ho epsilon address)
  let ep := Fin.cast (SourceLengths.fine_length he k h 1 (by omega)) (MersenneCodeOrigins.endpoint data epsilon)
  have hbig : 2∣2^(k+h+3) := by
    exact Nat.pow_dvd_pow 2 (show 1≤k+h+3 by omega)
  have hsmall : 2∣2^(k+h+1) := by
    exact Nat.pow_dvd_pow 2 (show 1≤k+h+1 by omega)
  have hcode : (MersenneCodeOrigins.endpoint data epsilon).val%2=
      (DenseSourceMarks.code 1 (by omega) epsilon address).val%2 := by
    have hc := congrArg (fun n=>n%2) (MersenneCodeOrigins.endpoint_code data epsilon)
    rw [Nat.mod_mod_of_dvd _ hbig] at hc
    exact hc.trans (code_mod_two (by omega) exceptional epsilon address)
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
    MersennePhysicalIncidence.orientedSource,data] using hg

/-- Exactly one actual Mersenne coordinate-zero grid owner within each
fixed twin/high-address group, derived from the actual causal decoder. -/
theorem unique_grid_owner (epsilon : Bool) (high : Address (k+h)) (z : Fin 2)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ∃address, InGroup 1 high address ∧
      ((MersennePhysicalIncidence.orientedSource he C k h hk hh room S ho hb exceptional epsilon address z).position v).val%2=0 ∧
      ∀address', InGroup 1 high address'→
        ((MersennePhysicalIncidence.orientedSource he C k h hk hh room S ho hb exceptional epsilon address' z).position v).val%2=0→address'=address := by
  obtain ⟨address,hgroup,hown,hu⟩ := SourceAnchorGroups.unique_group_owner he C k h 1
    (by omega) S ho epsilon high v (signedOffset (2^(k+h+1)) 1 z.val epsilon)
  refine ⟨address,hgroup,(anchor_iff he C k h hk hh room S ho hb exceptional epsilon address z v).mpr hown,?_⟩
  intro address' hgroup' hgrid'
  exact hu address' hgroup' ((anchor_iff he C k h hk hh room S ho hb exceptional epsilon address' z v).mp hgrid')

end Coordinates

section Factors
variable {V : Type} {R : V→V→Prop} {m e : Nat}
  (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)
  (k h : Nat) (hk : 2≤k) (hh : 0<h)
  (room : 2^(k+h+3)∣lengthPower (2^e) k)
  (S : Fin m→Address k→Fin (2^(e*2^k))→Bool)
  (ho : ∀f address, Profile.cardinality (S f address)%2=1)
  (hb : ∀f, ∀address : Address (k+h), Profile.prefixCount (S f (lowerAddress address)) 2=1)
  (exceptional : Bool)

noncomputable def startsFor (z : Fin 2) (cfg : Fin m×Bool×Address (k+h)) :
    Fin (2^(e*2^(k+h+1)-1)*2) :=
  let data := MersenneCodeOrigins.family he (D.cycles cfg.1).toClockData k h (by omega)
    hh room (S cfg.1) (ho cfg.1) (hb cfg.1) exceptional cfg.2.2
  OrientedClock.index (Nat.mul_pos (Nat.two_pow_pos _) (by decide : 0<2))
    (Fin.cast (SourceLengths.fine_length he k h 1 (by omega)) (MersenneCodeOrigins.endpoint data cfg.2.1))
    (!cfg.2.1) (BaselinePhysical.threshold (Nat.two_pow_pos _) z)

noncomputable def starts (z : Fin 2) (q : Fin (count (2*count m k) h)) :
    Fin (2^(e*2^(k+h+1)-1)*2) :=
  startsFor D he k h hk hh room S ho hb exceptional z (SourceOrientedFactors.configuration k h q)

/-- Genuine full Hamilton partition using the actual Mersenne occurrence
origins and twin directions. No output adjacency/partition premise. -/
noncomputable def factors (z : Fin 2) :
    DecompositionData (VertexPower (VertexPower V k×VertexPower V k) h)
      (relation (ProductAdjacent (relation R k)) h) (count (2*count m k) h)
      (2^(e*2^(k+h+1)-1)*2) (Nat.mul_pos (Nat.two_pow_pos _) (by decide : 0<2)) :=
  HamiltonOrient.factors (SourceOrientedFactors.base D he k h 1 (by omega) S ho)
    (starts D he k h hk hh room S ho hb exceptional z) (SourceOrientedFactors.directions k h)

/-- Owned actual Hamilton factor and geometric Mersenne clock coincide. -/
theorem clock_eq (z : Fin 2) (f : Fin m) (epsilon : Bool) (address : Address (k+h)) :
    ((factors D he k h hk hh room S ho hb exceptional z).cycles
      (SourceFactors.index k h f epsilon address)).toClockData=
      MersennePhysicalIncidence.orientedSource he (D.cycles f).toClockData k h hk hh room
        (S f) (ho f) (hb f) exceptional epsilon address z := by
  unfold factors HamiltonOrient.factors
  change OrientedClock.clock _
    (((SourceOrientedFactors.base D he k h 1 (by omega) S ho).cycles
      (SourceFactors.index k h f epsilon address)).toClockData)
    (starts D he k h hk hh room S ho hb exceptional z (SourceFactors.index k h f epsilon address))
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
      (((factors D he k h hk hh room S ho hb exceptional z).cycles i).position v).val%2=0 := by
  let key := SourceHostPartition.indexKey j
  obtain ⟨address,hgroup,hgrid,_⟩ := unique_grid_owner he (D.cycles key.1).toClockData
    k h hk hh room (S key.1) (ho key.1) (hb key.1) exceptional key.2.1
    (highAddress 1 (by omega) key.2.2) z v
  refine ⟨SourceFactors.index k h key.1 key.2.1 address,?_,?_⟩
  · unfold association
    rw [SourceHostPartition.association_index,
      SourceHostPartition.highKey_eq 1 (by omega) key.2.2 address hgroup]
    exact SourceHostPartition.keyIndex_indexKey j
  · rw [←clock_eq D he k h hk hh room S ho hb exceptional z] at hgrid
    exact hgrid

/-- Actual coordinate-zero ownership remains unique although the full
Mersenne occurrence code itself is not injective. -/
theorem representative_unique (z : Fin 2) (i i' : Fin (count (2*count m k) h))
    (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (hai : association k h hk i=association k h hk i')
    (hi : (((factors D he k h hk hh room S ho hb exceptional z).cycles i).position v).val%2=0)
    (hi' : (((factors D he k h hk hh room S ho hb exceptional z).cycles i').position v).val%2=0) : i=i' := by
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
  rw [←hci,clock_eq D he k h hk hh room S ho hb exceptional z] at hi
  rw [←hci',clock_eq D he k h hk hh room S ho hb exceptional z,←hf,←heps] at hi'
  obtain ⟨owner,_,_,hu⟩ := unique_grid_owner he (D.cycles cfg.1).toClockData k h hk hh room
    (S cfg.1) (ho cfg.1) (hb cfg.1) exceptional cfg.2.1
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

/-- Actual Mersenne anchored host, with the constructed assigned H factor. -/
noncomputable def Host (z : Fin 2) (i : Fin (count (2*count m k) h))
    (x y : VertexPower (VertexPower V k×VertexPower V k) h×W) : Prop :=
  (x.2=y.2 ∧ SourceHostPartition.FactorEdge (factors D he k h hk hh room S ho hb exceptional z) i x.1 y.1) ∨
  (x.1=y.1 ∧ (((factors D he k h hk hh room S ho hb exceptional z).cycles i).position x.1).val%2=0 ∧
    SourceHostPartition.FactorEdge H (association k h hk i) x.2 y.2)

theorem host_subset (z : Fin 2) {i : Fin (count (2*count m k) h)}
    {x y : VertexPower (VertexPower V k×VertexPower V k) h×W}
    (hi : Host D he k h hk hh room S ho hb exceptional H z i x y) :
    AnchoredEmbedding.ProductRelation (relation (ProductAdjacent (relation R k)) h) T x y := by
  rcases hi with ⟨hw,hi⟩ | ⟨hv,_,hi⟩
  · exact Or.inl ⟨hw,SourceHostPartition.factorEdge_relation _ hi⟩
  · exact Or.inr ⟨hv,SourceHostPartition.factorEdge_relation _ hi⟩

theorem host_cover (z : Fin 2) {x y : VertexPower (VertexPower V k×VertexPower V k) h×W}
    (hedge : AnchoredEmbedding.ProductRelation (relation (ProductAdjacent (relation R k)) h) T x y) :
    ∃i : Fin (count (2*count m k) h), Host D he k h hk hh room S ho hb exceptional H z i x y := by
  rcases hedge with ⟨hw,hedge⟩ | ⟨hv,hedge⟩
  · obtain ⟨i,t,ht⟩ := (factors D he k h hk hh room S ho hb exceptional z).cover x.1 y.1 hedge
    exact ⟨i,Or.inl ⟨hw,t,ht⟩⟩
  · obtain ⟨j,t,ht⟩ := H.cover x.2 y.2 hedge
    obtain ⟨i,hai,hgrid⟩ := representative_cover D he k h hk hh room S ho hb exceptional z j x.1
    exact ⟨i,Or.inr ⟨hv,hgrid,by rw [hai]; exact ⟨t,ht⟩⟩⟩

theorem host_unique (z : Fin 2) {i i' : Fin (count (2*count m k) h)}
    {x y : VertexPower (VertexPower V k×VertexPower V k) h×W}
    (hi : Host D he k h hk hh room S ho hb exceptional H z i x y)
    (hi' : Host D he k h hk hh room S ho hb exceptional H z i' x y) : i=i' := by
  rcases hi with ⟨hw,hi⟩ | ⟨hv,hgi,hi⟩
  · rcases hi' with ⟨_,hi'⟩ | ⟨hv,_,_⟩
    · exact SourceHostPartition.factorEdge_unique _ hi hi'
    · have hg := SourceHostPartition.factorEdge_relation _ hi
      rw [hv] at hg
      exact False.elim ((factors D he k h hk hh room S ho hb exceptional z).loopfree _ hg)
  · rcases hi' with ⟨_,hi'⟩ | ⟨_,hgi',hi'⟩
    · have hg := SourceHostPartition.factorEdge_relation _ hi'
      rw [hv] at hg
      exact False.elim ((factors D he k h hk hh room S ho hb exceptional z).loopfree _ hg)
    · exact representative_unique D he k h hk hh room S ho hb exceptional z i i' x.1
        (SourceHostPartition.factorEdge_unique H hi hi') hgi hgi'

theorem host_partition (z : Fin 2) (x y : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    AnchoredEmbedding.ProductRelation (relation (ProductAdjacent (relation R k)) h) T x y ↔
    ∃i : Fin (count (2*count m k) h), Host D he k h hk hh room S ho hb exceptional H z i x y ∧
      ∀i', Host D he k h hk hh room S ho hb exceptional H z i' x y→i'=i := by
  constructor
  · intro hedge
    obtain ⟨i,hi⟩ := host_cover D he k h hk hh room S ho hb exceptional H z hedge
    exact ⟨i,hi,fun _ hi'=>host_unique D he k h hk hh room S ho hb exceptional H z hi' hi⟩
  · rintro ⟨_,hi,_⟩
    exact host_subset D he k h hk hh room S ho hb exceptional H z hi
end Host

end Factors
#print axioms host_partition
#print axioms representative_unique
#print axioms anchor_iff
#print axioms unique_grid_owner
#print axioms code_mod_two
#print axioms factors
#print axioms clock_eq
end ErdePaths.MersenneOrientedFactors
