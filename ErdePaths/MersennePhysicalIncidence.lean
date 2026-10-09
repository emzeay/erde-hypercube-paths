import ErdePaths.MersennePhysicalUnmarks
import ErdePaths.MersenneCodeOrigins
import ErdePaths.MersenneComplement
import ErdePaths.SourceLengths

namespace ErdePaths.MersennePhysicalIncidence
open SourceClock SourceProfile SquareLift OrientedClock HierarchicalDecode
attribute [local instance] Classical.propDecidable

private theorem threshold_iff {K : Nat} (_hK : 0<K) (x : Fin (K*2)) (z : Fin 2) :
    (∃i : Fin K, x=AnchoredEmbedding.positionEncode i z) ↔ x.val%2=z.val := by
  have hh := BaselineResidues.threshold_residue_iff (by decide : 0<2) (by decide : 0<1)
    x z (fun _=>True)
  constructor
  · intro hx
    obtain ⟨u,_,hu⟩ := hh.mp (by obtain ⟨i,hi⟩ := hx; exact ⟨i,hi,True.intro⟩)
    have hz : u.val=0 := by have := u.isLt; omega
    simpa only [hz,Nat.mul_zero,Nat.zero_add] using hu
  · intro hx
    obtain ⟨i,hi,_⟩ := hh.mpr ⟨⟨0,by decide⟩,True.intro,by simpa using hx⟩
    exact ⟨i,hi⟩

private theorem bit_zero_iff (n m : Nat) : n.testBit 0=m.testBit 0 ↔ n%2=m%2 := by
  have hn := Nat.mod_lt n (by decide : 0<2)
  have hm := Nat.mod_lt m (by decide : 0<2)
  simp only [Nat.testBit_zero,decide_eq_decide]
  omega

/-- Actual threshold eligibility from the literal full-cycle origin. -/
theorem physical_threshold {U : Type} {K : Nat} (hK : 0<K)
    (C : ClockData U (K*2)) (endpoint : Fin (K*2)) (z : Fin 2) (epsilon : Bool) (v : U) :
    let G := clock (Nat.mul_pos hK (by decide)) C
      (index (Nat.mul_pos hK (by decide)) endpoint (!epsilon) (BaselinePhysical.threshold hK z)) epsilon
    (∃i : Fin K, (G).position v=AnchoredEmbedding.positionEncode i z) ↔
      (C.position v).val.testBit 0=endpoint.val.testBit 0 := by
  dsimp only
  rw [threshold_iff hK,bit_zero_iff]
  have hh := BaselinePhysical.class_incidence (L:=1) hK (by decide) (by decide)
    (Nat.one_dvd K) C endpoint ⟨endpoint.val%2,Nat.mod_lt _ (by decide)⟩ rfl z epsilon v ⟨0,by decide⟩
  have hz : SourceStability.signedOffset 2 2 0 (!epsilon)=0 := by
    cases epsilon <;> simp [SourceStability.signedOffset,shiftedResidue]
  simpa only [Nat.mul_one,Nat.mul_zero,Nat.zero_add,hz,shiftedResidue,Nat.zero_mod,
    Nat.sub_zero,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod] using hh

private theorem exponent_room (t : Nat) : t+1≤2^t := by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos t; omega

private theorem coarse_div {e : Nat} (he : 2≤e) (k h : Nat) :
    2*2^(k+h+1)∣2^(e*2^(k+h+1)-1) := by
  have hp := exponent_room (k+h+1)
  have hm := Nat.mul_le_mul_right (2^(k+h+1)) he
  have hd : k+h+2≤e*2^(k+h+1)-1 := by omega
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.pow_dvd_pow 2 hd

noncomputable def orientedSource {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (exceptional epsilon : Bool) (a : Address (k+h)) (z : Fin 2) :
    ClockData (VertexPower (VertexPower V k×VertexPower V k) h)
      (2^(e*2^(k+h+1)-1)*2) :=
  let D := MersenneCodeOrigins.family he C k h (by omega) hh room S ho hbalance exceptional a
  let raw := castClock (SourceLengths.fine_length he k h 1 (by omega))
    (SourceProfile.clock he C k h S ho epsilon a)
  let ep := Fin.cast (SourceLengths.fine_length he k h 1 (by omega))
    (MersenneCodeOrigins.endpoint D epsilon)
  let hK := Nat.two_pow_pos (e*2^(k+h+1)-1)
  clock (Nat.mul_pos hK (by decide)) raw
    (index (Nat.mul_pos hK (by decide)) ep (!epsilon) (BaselinePhysical.threshold hK z)) epsilon

section Source
variable {V : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k h : Nat) (hk : 2≤k) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
  (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
  (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
  (exceptional epsilon : Bool) (a : Address (k+h)) (z : Fin 2)
local notation "K" => 2^(e*2^(k+h+1)-1)
local notation "periodN" => 2^(k+h+1)
local notation "D" => MersenneCodeOrigins.family he C k h (by omega) hh room S ho hbalance exceptional a
local notation "raw" => castClock (SourceLengths.fine_length he k h 1 (by omega)) (SourceProfile.clock he C k h S ho epsilon a)
local notation "ep" => Fin.cast (SourceLengths.fine_length he k h 1 (by omega)) (MersenneCodeOrigins.endpoint D epsilon)
local notation "G" => orientedSource he C k h hk hh room S ho hbalance exceptional epsilon a z

private theorem full_period : 2^(k+h+3)=4*periodN := by
  have ht : k+h+3=(k+h+1)+2 := by omega
  rw [ht,Nat.pow_add]
  simp [Nat.mul_comm]

private theorem endpoint_zero_bit : (ep).val.testBit 0=a ⟨0,by omega⟩ := by
  have hc := MersenneCodeOrigins.endpoint_code D epsilon
  have hb := congrArg (fun n=>n.testBit 0) hc
  have hi : decide (0<k+h+3)=true := by simp
  simp only [Nat.testBit_mod_two_pow,hi,Bool.true_and] at hb
  have ha := congrFun (MersenneCode.code_bits (by omega : 2≤k+h) exceptional epsilon a) ⟨0,by omega⟩
  have ha' : (MersenneCode.code (by omega : 2≤k+h) exceptional epsilon a).val.testBit 0=a ⟨0,by omega⟩ := by
    simpa only [binaryTuple,MersenneCode.codeBits,↓reduceIte] using ha
  exact hb.trans ha'

theorem threshold_eligible (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (∃i : Fin K, (G).position v=AnchoredEmbedding.positionEncode i z) ↔
      MersenneComplement.Eligible he C k h (by omega) S ho epsilon v a := by
  have hh' := physical_threshold (Nat.two_pow_pos _) raw ep z epsilon v
  dsimp only [orientedSource] at hh' ⊢
  rw [endpoint_zero_bit he C k h hk hh room S ho hbalance exceptional epsilon a] at hh'
  simpa only [MersenneComplement.Eligible,castClock_position,Fin.val_cast] using hh'

theorem unmark_removed (v : VertexPower (VertexPower V k×VertexPower V k) h) (row : Fin B) :
    ((∃i : Fin K, (G).position v=AnchoredEmbedding.positionEncode i z) ∧
      ¬AACMarkIntervals.IsMark (Nat.two_pow_pos _)
        (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN)) w.1) z ((G).position v,row)) ↔
      MersenneComplement.Removed he C k h (by omega) S ho exceptional epsilon v a := by
  have hperiod := full_period k h
  have hc : (ep).val%(4*periodN)=(Fin.cast hperiod (MersenneCode.code (by omega : 2≤k+h) exceptional epsilon a)).val := by
    simpa only [Fin.val_cast,←hperiod] using MersenneCodeOrigins.endpoint_code D epsilon
  have hP : 8≤periodN := Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)
  have ht := MersennePhysicalUnmarks.physical_unmarks (Nat.two_pow_pos _) hP (coarse_div he k h)
    raw ep (Fin.cast hperiod (MersenneCode.code (by omega : 2≤k+h) exceptional epsilon a)) hc z epsilon v row
  dsimp only [orientedSource] at ht ⊢
  simpa only [MersenneComplement.Removed,MersenneComplement.RemovedAt,MersenneComplement.rawValue,
    castClock_position,Fin.val_cast,hperiod] using ht

theorem mark_retained (v : VertexPower (VertexPower V k×VertexPower V k) h) (row : Fin B) :
    AACMarkIntervals.IsMark (Nat.two_pow_pos _)
      (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN)) w.1) z ((G).position v,row) ↔
      MersenneComplement.Eligible he C k h (by omega) S ho epsilon v a ∧
      ¬MersenneComplement.Removed he C k h (by omega) S ho exceptional epsilon v a := by
  have ht := threshold_eligible he C k h hk hh room S ho hbalance exceptional epsilon a z v
  have hu := unmark_removed he C k h hk hh room S ho hbalance exceptional epsilon a z v row
  have hm : AACMarkIntervals.IsMark (Nat.two_pow_pos _)
      (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN)) w.1) z ((G).position v,row) →
      ∃i : Fin K, (G).position v=AnchoredEmbedding.positionEncode i z := by
    rintro ⟨i,j,hx,_⟩
    exact ⟨i,(Prod.mk.inj hx).1⟩
  constructor
  · intro hh'
    refine ⟨ht.mp (hm hh'),?_⟩
    intro hr
    exact (hu.mpr hr).2 hh'
  · rintro ⟨he',hn⟩
    apply Classical.byContradiction
    intro hnm
    exact hn (hu.mp ⟨ht.mpr he',hnm⟩)
end Source

/-- Literal geometric incidence across every full numeric configuration.
The actual H row may depend arbitrarily on the configuration. -/
noncomputable def multiplicity {V : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (exceptional : Bool) (z : Fin 2) (rows : Vertex (k+h+1)→Fin B)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) : Nat :=
  (List.finRange (2^(k+h+1))).countP (fun q=>decide
    (AACMarkIntervals.IsMark (Nat.two_pow_pos (e*2^(k+h+1)-1))
      (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
        (TurnPatterns.long (P:=2^(k+h+1))) w.1) z
      ((orientedSource he C k h hk hh room S ho hbalance exceptional
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z).position v,rows q)))

theorem multiplicity_retained {V : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (exceptional : Bool) (z : Fin 2) (rows : Vertex (k+h+1)→Fin B)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    multiplicity he C k h hk hh room S ho hbalance exceptional z rows v=
      (List.finRange (2^(k+h+1))).countP (fun q=>decide
        (MersenneComplement.Eligible he C k h hk S ho (DenseSourceCounts.epsilonOf 1 q) v (DenseSourceCounts.addressOf 1 q) ∧
         ¬MersenneComplement.Removed he C k h hk S ho exceptional (DenseSourceCounts.epsilonOf 1 q) v (DenseSourceCounts.addressOf 1 q))) := by
  apply List.countP_congr
  intro q hq
  simp only [decide_eq_true_eq]
  exact mark_retained he C k h hk hh room S ho hbalance exceptional
    (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v (rows q)

/-- Exceptional small-base actual physical long marks have exactly L−1
incidences, derived from the unique actual numeric removal owner. -/
theorem small_multiplicity {V : Type} {B : Nat} (C : ClockData V (2^2)) (t h : Nat)
    (hh : 0<h) (room : 2^(t+2+h+3)∣lengthPower (2^2) (t+2))
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (t+2+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (z : Fin 2) (rows : Vertex (t+2+h+1)→Fin B)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    multiplicity (by omega) C (t+2) h (by omega) hh room S ho hbalance true z rows v=2^(t+2+h)-1 := by
  rw [multiplicity_retained]
  exact MersenneComplement.small_retained_count C t h (by omega) S ho v

/-- Larger-base actual physical long marks have the same exact L−1 count
with the ordinary code, uniformly in every hierarchy depth. -/
theorem large_multiplicity {V : Type} {e B : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (z : Fin 2) (rows : Vertex (k+h+1)→Fin B)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    multiplicity (by omega) C k h hk hh room S ho hbalance false z rows v=2^(k+h)-1 := by
  rw [multiplicity_retained]
  exact MersenneComplement.large_retained_count he C k h hk (by omega) S ho v

#print axioms small_multiplicity
#print axioms large_multiplicity
#print axioms physical_threshold
#print axioms threshold_eligible
#print axioms unmark_removed
#print axioms mark_retained
end ErdePaths.MersennePhysicalIncidence
