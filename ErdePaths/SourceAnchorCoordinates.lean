import ErdePaths.SourceCodeOrigins
import ErdePaths.SourceAnchorGroups

namespace ErdePaths.SourceAnchorCoordinates
open SourceClock SourceProfile SquareLift OrientedClock AACResidueBridge SourceStability

/-- The actual rotated/reversed coordinate zero class is the raw origin
class. The old-grid sign is epsilon, opposite the new-mark sign !epsilon. -/
theorem grid_residue_iff {V : Type} {N A : Nat} (hN : 0<N) (hA : 0<A) (hd : A∣N)
    (C : ClockData V N) (c z : Fin N) (epsilon : Bool) (v : V) :
    ((OrientedClock.clock hN C (OrientedClock.index hN c (!epsilon) z) epsilon).position v).val%A=0 ↔
    shiftedResidue A (signedOffset A 1 z.val epsilon) (C.position v).val=c.val%A := by
  let G := OrientedClock.clock hN C (OrientedClock.index hN c (!epsilon) z) epsilon
  let start := OrientedClock.index hA (reduce hA c) (!epsilon) (reduce hA z)
  have hx : reduce hA (C.position v)=OrientedClock.index hA start epsilon (reduce hA (G.position v)) := by
    have hh := congrArg (fun w => reduce hA (C.position w)) (G.cycle_position v)
    simp only [G,OrientedClock.clock,C.position_cycle] at hh
    rw [reduce_index hN hA hd,reduce_index hN hA hd] at hh
    exact hh.symm
  have hz : OrientedClock.index hA start epsilon ⟨0,hA⟩=start := by
    cases epsilon <;> simp [OrientedClock.index,forward_zero,backward_zero]
  have he : reduce hA (C.position v)=start ↔ reduce hA (G.position v)=⟨0,hA⟩ := by
    rw [hx]
    constructor
    · intro hh
      apply AACResidueBridge.index_injective hA start epsilon
      exact hh.trans hz.symm
    · intro hh; rw [hh]; exact hz
  have hs := shifted_signed_iff hA (reduce hA c) (reduce hA (C.position v)) (reduce hA z) (!epsilon)
  have hdelta : signedOffset A 1 (reduce hA z).val (!(!epsilon))=signedOffset A 1 z.val epsilon := by
    cases epsilon <;> simp [signedOffset,reduce,shiftedResidue]
  rw [hdelta] at hs
  have hs' : shiftedResidue A (signedOffset A 1 z.val epsilon) (C.position v).val=c.val%A ↔
      reduce hA (C.position v)=start := by
    simpa only [start,reduce,shiftedResidue,Nat.mod_add_mod] using hs
  rw [hs',he]
  constructor
  · intro hh; exact Fin.ext hh
  · intro hh; exact congrArg Fin.val hh

/-- Honest reduction of arithmetic subtraction to a dividing modulus. -/
theorem shifted_reduce {P A : Nat} (hP : 0<P) (hA : 0<A) (hd : A∣P) (delta x : Nat) :
    shiftedResidue P delta x%A=shiftedResidue A delta x := by
  simp only [shiftedResidue,Nat.mod_mod_of_dvd _ hd]
  have hh := PairedArc.difference_phase (i:=x) hA hd (Nat.mod_lt delta hP)
  rw [Nat.add_comm x (P-delta%P),Nat.add_comm x (A-delta%A),hh,Nat.mod_mod_of_dvd _ hd]
  exact Nat.add_mod_mod _ _ _

/-- Reducing a signed offset preserves its literal sign, including all
subtraction wraps and unreduced offsets. -/
theorem signed_reduce {P A : Nat} (hP : 0<P) (hA : 0<A) (hd : A∣P)
    (z : Nat) (epsilon : Bool) : signedOffset P 1 z epsilon%A=signedOffset A 1 z epsilon := by
  cases epsilon
  · simp [signedOffset,Nat.mod_mod_of_dvd _ hd]
  · simp only [signedOffset,ite_true,Nat.one_mul]
    exact shifted_reduce hP hA hd z 0

/-- Source-code-sized shifts reduce to the exact old-grid modulus, retaining
its opposite-to-mark sign convention. -/
theorem signed_shift_reduce {P A : Nat} (hP : 0<P) (hA : 0<A) (hd : A∣P)
    (z x : Nat) (epsilon : Bool) :
    shiftedResidue P (signedOffset P 1 z epsilon) x%A=
      shiftedResidue A (signedOffset A 1 z epsilon) x := by
  rw [shifted_reduce hP hA hd]
  simp only [shiftedResidue]
  rw [signed_reduce hP hA hd]
  cases epsilon <;> simp [signedOffset,shiftedResidue]

/-- Actual coarse-grid vertex membership is precisely coordinate zero modulo
its subdivision length, using the genuine inverse clock. -/
theorem anchor_vertices_iff {V : Type} {K A : Nat} (hA : 0<A) (G : ClockData V (K*A)) (v : V) :
    (∃i : Fin K, G.cycle (AnchoredEmbedding.positionEncode i ⟨0,hA⟩)=v) ↔
      (G.position v).val%A=0 := by
  constructor
  · rintro ⟨i,hi⟩
    have hp := congrArg G.position hi
    rw [G.position_cycle] at hp
    rw [←hp]
    simp [AnchoredEmbedding.positionEncode]
  · intro hm
    let p := AnchoredEmbedding.positionDecode hA (G.position v)
    have hz : p.2=(⟨0,hA⟩ : Fin A) := Fin.ext hm
    refine ⟨p.1,?_⟩
    rw [←hz,AnchoredEmbedding.positionEncode_decode,G.cycle_position]

section Source
variable {V : Type} {e u : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
  (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
  (S : HierarchicalDecode.Address a→Fin (2^(e*2^a))→Bool)
  (ho : ∀address, Profile.cardinality (S address)%2=1)
  (hbalance : ∀address : HierarchicalDecode.Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)

/-- The actual constructed source factor's coordinate-zero grid is exactly
the restricted old-anchor decoder class. No representative equivalence or
physical endpoint phase premise is supplied by the caller. -/
theorem source_anchor_iff (epsilon : Bool) (address : HierarchicalDecode.Address (a+h))
    (z : Fin (2^r)) (v : VertexPower (VertexPower V a×VertexPower V a) h) :
    ((SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance epsilon address z).position v).val%(2^r)=0 ↔
    SourceAnchorGroups.Owns he C a h r (by omega) S ho epsilon v
      (signedOffset (2^(a+h+1)) 1 z.val epsilon) address := by
  let D := SourceCodeOrigins.family he C a h r hr hh room hA S ho hbalance address
  let raw := castClock (SourceLengths.fine_length he a h r hr) (SourceProfile.clock he C a h S ho epsilon address)
  let endpoint := Fin.cast (SourceLengths.fine_length he a h r hr) (SourceCodeOrigins.endpoint D epsilon)
  have hdiv : 2^r∣2^(a+h+1) := Nat.pow_dvd_pow 2 (by omega)
  have hc : (SourceCodeOrigins.endpoint D epsilon).val%(2^r)=
      (DenseSourceMarks.code r hr epsilon address).val%(2^r) := by
    have hh := congrArg (fun n => n%(2^r)) (SourceCodeOrigins.endpoint_code D epsilon)
    simpa only [Nat.mod_mod_of_dvd _ hdiv] using hh
  have hg := grid_residue_iff
    (Nat.mul_pos (Nat.two_pow_pos (e*2^(a+h+1)-r)) (Nat.two_pow_pos r))
    (Nat.two_pow_pos r) (Nat.dvd_mul_left (2^r) (2^(e*2^(a+h+1)-r)))
    raw endpoint (BaselinePhysical.threshold (Nat.two_pow_pos _) z) epsilon v
  change _ ↔ SourceAnchorGroups.Owns he C a h r (by omega) S ho epsilon v _ address
  unfold SourceAnchorGroups.Owns shiftedValue
  rw [signed_shift_reduce (Nat.two_pow_pos _) (Nat.two_pow_pos r) hdiv]
  have heq : shiftedResidue (2^r) (signedOffset (2^r) 1 z.val epsilon)
      ((SourceProfile.clock he C a h S ho epsilon address).position v).val=
      (DenseSourceMarks.code r hr epsilon address).val%(2^r) ↔
    shiftedResidue (2^r) (signedOffset (2^r) 1 z.val epsilon)
      ((SourceProfile.clock he C a h S ho epsilon address).position v).val=
      (SourceCodeOrigins.endpoint D epsilon).val%(2^r) := by rw [hc]
  rw [heq]
  simpa only [raw,endpoint,castClock_position,Fin.val_cast,BaselinePhysical.threshold,SourceCodeOrigins.orientedSource,D] using hg

/-- Literal actual old-anchor vertices of the constructed source cycle are
exactly its restricted-decoder class, without a representative hypothesis. -/
theorem source_vertices_iff (epsilon : Bool) (address : HierarchicalDecode.Address (a+h))
    (z : Fin (2^r)) (v : VertexPower (VertexPower V a×VertexPower V a) h) :
    (∃i : Fin (2^(e*2^(a+h+1)-r)),
      (SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance epsilon address z).cycle
        (AnchoredEmbedding.positionEncode i ⟨0,Nat.two_pow_pos r⟩)=v) ↔
    SourceAnchorGroups.Owns he C a h r (by omega) S ho epsilon v
      (signedOffset (2^(a+h+1)) 1 z.val epsilon) address := by
  rw [anchor_vertices_iff (Nat.two_pow_pos r),source_anchor_iff he C a h r hr hh room hA S ho hbalance]

/-- Every physical first-axis vertex lies in the actual coordinate-zero grid
of exactly one source factor within each fixed-twin/high-address group. -/
theorem unique_grid_owner (epsilon : Bool) (high : HierarchicalDecode.Address (a+h))
    (z : Fin (2^r)) (v : VertexPower (VertexPower V a×VertexPower V a) h) :
    ∃address, SourceAnchorGroups.InGroup r high address ∧
      ((SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance epsilon address z).position v).val%(2^r)=0 ∧
      ∀address', SourceAnchorGroups.InGroup r high address'→
        ((SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance epsilon address' z).position v).val%(2^r)=0→address'=address := by
  obtain ⟨address,hg,ho',hu⟩ := SourceAnchorGroups.unique_group_owner he C a h r (by omega) S ho
    epsilon high v (signedOffset (2^(a+h+1)) 1 z.val epsilon)
  refine ⟨address,hg,(source_anchor_iff he C a h r hr hh room hA S ho hbalance epsilon address z v).mpr ho',?_⟩
  intro address' hg' hc
  exact hu address' hg' ((source_anchor_iff he C a h r hr hh room hA S ho hbalance epsilon address' z v).mp hc)

end Source
#print axioms grid_residue_iff
#print axioms source_vertices_iff
#print axioms source_anchor_iff
#print axioms unique_grid_owner
end ErdePaths.SourceAnchorCoordinates
