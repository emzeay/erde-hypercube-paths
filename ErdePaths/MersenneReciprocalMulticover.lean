import ErdePaths.MersennePhysicalIncidence
import ErdePaths.SourceReciprocalExchange
import ErdePaths.DenseCodePairs
import ErdePaths.HamiltonCommonLast
import ErdePaths.SourceMarkMulticover

namespace ErdePaths.MersenneReciprocalMulticover
open SourceClock SourceProfile SquareLift HierarchicalDecode PairedArc
attribute [local instance] Classical.propDecidable

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

section Source
variable {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k h : Nat) (hk : 2≤k) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
  (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
  (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
  (exceptional : Bool)
local notation "K" => 2^(e*2^(k+h+1)-1)
local notation "periodN" => 2^(k+h+1)
local notation "hN" => Nat.mul_pos (Nat.two_pow_pos (e*2^(k+h+1)-1)) (by decide : 0<2)

noncomputable def arc (epsilon : Bool) (a : Address (k+h)) :
    DirectedArc hN (castClock (SourceLengths.fine_length he k h 1 (by omega))
      (SourceProfile.clock he C k h S ho epsilon a)) 2 := by
  let D := MersenneCodeOrigins.family he C k h (by omega) hh room S ho hbalance exceptional a
  cases epsilon
  · exact SourceReciprocalExchange.castArc (SourceLengths.fine_length he k h 1 (by omega)) rfl _ hN _ D.arcFalse
  · exact SourceReciprocalExchange.castArc (SourceLengths.fine_length he k h 1 (by omega)) rfl _ hN _ D.arcTrue

theorem arc_start_equal (a : Address (k+h)) :
    (arc he C k h hk hh room S ho hbalance exceptional false a).vertex ⟨0,by omega⟩=
    (arc he C k h hk hh room S ho hbalance exceptional true a).vertex ⟨0,by omega⟩ := by
  simp only [arc,SourceReciprocalExchange.castArc_zero]
  exact (MersenneCodeOrigins.family he C k h (by omega) hh room S ho hbalance exceptional a).start_equal

theorem arc_end_equal (a : Address (k+h)) :
    (arc he C k h hk hh room S ho hbalance exceptional false a).vertex ⟨2,by omega⟩=
    (arc he C k h hk hh room S ho hbalance exceptional true a).vertex ⟨2,by omega⟩ := by
  simp only [arc,SourceReciprocalExchange.castArc_last]
  exact (MersenneCodeOrigins.family he C k h (by omega) hh room S ho hbalance exceptional a).end_equal

theorem true_clock (a : Address (k+h)) (z : Fin 2) :
    MersennePhysicalIncidence.orientedSource he C k h hk hh room S ho hbalance exceptional true a z=
      ReciprocalEndpoints.forwardClock hN
        (castClock (SourceLengths.fine_length he k h 1 (by omega)) (SourceProfile.clock he C k h S ho true a))
        (arc he C k h hk hh room S ho hbalance exceptional true a)
        (AnchoredEmbedding.positionEncode (⟨0,Nat.two_pow_pos _⟩ : Fin K) z) := by
  simp only [MersennePhysicalIncidence.orientedSource,ReciprocalEndpoints.forwardClock,
    OrientedClock.index,Bool.not_true,Bool.false_eq_true,ite_false,MersenneCodeOrigins.endpoint,
    ite_true,arc,SourceReciprocalExchange.castArc_last,SourceReciprocalExchange.castClock_position_eq,
    SourceReciprocalExchange.threshold_eq]

theorem false_clock (a : Address (k+h)) (z : Fin 2) :
    MersennePhysicalIncidence.orientedSource he C k h hk hh room S ho hbalance exceptional false a z=
      ReciprocalEndpoints.reverseClock hN
        (castClock (SourceLengths.fine_length he k h 1 (by omega)) (SourceProfile.clock he C k h S ho false a))
        (arc he C k h hk hh room S ho hbalance exceptional false a)
        (AnchoredEmbedding.positionEncode (⟨0,Nat.two_pow_pos _⟩ : Fin K) z) := by
  simp only [MersennePhysicalIncidence.orientedSource,ReciprocalEndpoints.reverseClock,
    OrientedClock.index,Bool.not_false,MersenneCodeOrigins.endpoint,Bool.false_eq_true,
    ite_false,ite_true,arc,SourceReciprocalExchange.castArc_zero,SourceReciprocalExchange.castClock_position_eq,
    SourceReciprocalExchange.threshold_eq]

noncomputable def markSet (H : Bool→Address (k+h)→ClockData W B) (post epsilon : Bool)
    (a : Address (k+h)) (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) : Prop :=
  let G := MersennePhysicalIncidence.orientedSource he C k h hk hh room S ho hbalance exceptional epsilon a z
  let hK := Nat.two_pow_pos (e*2^(k+h+1)-1)
  let t := TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN))
  AACMarkExchange.ImageSet (ReciprocalEndpoints.host G (H epsilon a))
    (AACMarkIntervals.IsMark hK (if post then AACInduction.turnsAfter hK t (B-1) else fun w=>t w.1) z) v

private theorem long_seams :
    let t : Fin K→Bool := TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN))
    t ⟨0,Nat.two_pow_pos _⟩=false ∧
    t ⟨1,by have := SourceLengths.coarse_size he k h 1 (by omega); omega⟩=false ∧
    t (predecessor (Nat.two_pow_pos _) ⟨0,Nat.two_pow_pos _⟩)=true := by
  have hp : 8≤periodN := Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)
  dsimp only
  constructor
  · rw [TurnPatterns.repeated_zero]; exact TurnPatterns.long_zero hp
  constructor
  · unfold TurnPatterns.repeated
    have ht : (⟨1%(2*periodN),Nat.mod_lt _ (Nat.mul_pos (by decide) (Nat.two_pow_pos _))⟩ : Fin (2*periodN))=
        ⟨1,by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [ht]; exact TurnPatterns.long_one hp
  · have hs : predecessor (Nat.two_pow_pos _) (⟨0,Nat.two_pow_pos _⟩ : Fin K)=⟨K-1,by have := Nat.two_pow_pos (e*2^(k+h+1)-1); omega⟩ := by
      apply Fin.ext; simp [predecessor,Nat.mod_eq_of_lt (show K-1<K by have := Nat.two_pow_pos (e*2^(k+h+1)-1); omega)]
    rw [hs,TurnPatterns.repeated_last _ (Nat.two_pow_pos _) (coarse_div he k h)]
    exact TurnPatterns.long_last hp

/-- Actual per-address surgery from constructed physical arcs and long
seam values; no exchanged-set or preservation premise. -/
theorem pair_preservation (hB : 0<B) (H : Bool→Address (k+h)→ClockData W B)
    (a : Address (k+h))
    (hlast : (H true a).cycle ⟨B-1,by omega⟩=(H false a).cycle ⟨B-1,by omega⟩)
    (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    AACMarkExchange.incidence (markSet he C k h hk hh room S ho hbalance exceptional H true true a z v)+
    AACMarkExchange.incidence (markSet he C k h hk hh room S ho hbalance exceptional H true false a z v)=
    AACMarkExchange.incidence (markSet he C k h hk hh room S ho hbalance exceptional H false true a z v)+
    AACMarkExchange.incidence (markSet he C k h hk hh room S ho hbalance exceptional H false false a z v) := by
  dsimp only [markSet]
  rw [true_clock he C k h hk hh room S ho hbalance exceptional a z,
    false_clock he C k h hk hh room S ho hbalance exceptional a z]
  have hs := long_seams he k h hk hh
  exact ReciprocalEndpoints.preservation
    (by have := SourceLengths.coarse_size he k h 1 (by omega); omega) (by decide) hB
    _ _ (arc he C k h hk hh room S ho hbalance exceptional true a)
    (arc he C k h hk hh room S ho hbalance exceptional false a)
    (arc_start_equal he C k h hk hh room S ho hbalance exceptional a).symm
    (arc_end_equal he C k h hk hh room S ho hbalance exceptional a).symm
    (H true a) (H false a) hlast z _ _ hs.1 hs.2.1 hs.2.2 hs.1 hs.2.1 hs.2.2 v

/-- Full numeric configuration postflip incidence equals the actual baseline
family; reserved-slot one enumeration is independently proved complete. -/
theorem postflip_eq_baseline (hB : 0<B) (H : Bool→Address (k+h)→ClockData W B)
    (hlast : ∀a, (H true a).cycle ⟨B-1,by omega⟩=(H false a).cycle ⟨B-1,by omega⟩)
    (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk hh room S ho hbalance exceptional H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk hh room S ho hbalance exceptional H false
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum := by
  apply DenseCodePairs.aggregate_exchange 1 (show 1<k+h+1 by omega)
    (fun eps a=>AACMarkExchange.incidence (markSet he C k h hk hh room S ho hbalance exceptional H true eps a z v))
    (fun eps a=>AACMarkExchange.incidence (markSet he C k h hk hh room S ho hbalance exceptional H false eps a z v))
  intro a
  have hp := pair_preservation he C k h hk hh room S ho hbalance exceptional hB H a (hlast a) z v
  simpa only [Nat.add_comm] using hp

private theorem indicator_sum {X : Type} (l : List X) (P : X→Prop) :
    (l.map (fun x=>if P x then 1 else 0)).sum=l.countP (fun x=>decide (P x)) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases hp : P x <;> simp [hp,ih,Nat.add_comm]

/-- Literal baseline physical images have the actual count supplied by
MersennePhysicalIncidence; even configuration-dependent H rows are allowed. -/
theorem baseline_eq_multiplicity (H : Bool→Address (k+h)→ClockData W B)
    (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk hh room S ho hbalance exceptional H false
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=
    MersennePhysicalIncidence.multiplicity he C k h hk hh room S ho hbalance exceptional z
      (fun q=>(H (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q)).position v.2) v.1 := by
  simp only [markSet,Bool.false_eq_true,ite_false,AACMarkExchange.incidence,
    SourceMarkMulticover.host_image_iff,MersennePhysicalIncidence.multiplicity]
  exact indicator_sum _ _

/-- Exact all-configuration postflip count derived from actual baseline and
actual source arc surgery, not a postflip multiplicity input. -/
theorem postflip_eq_multiplicity (hB : 0<B) (H : Bool→Address (k+h)→ClockData W B)
    (hlast : ∀a, (H true a).cycle ⟨B-1,by omega⟩=(H false a).cycle ⟨B-1,by omega⟩)
    (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk hh room S ho hbalance exceptional H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=
    MersennePhysicalIncidence.multiplicity he C k h hk hh room S ho hbalance exceptional z
      (fun q=>(H (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q)).position v.2) v.1 := by
  rw [postflip_eq_baseline he C k h hk hh room S ho hbalance exceptional hB H hlast z v]
  exact baseline_eq_multiplicity he C k h hk hh room S ho hbalance exceptional H z v

/-- Actual H decomposition data supplies the common physical last vertex
internally, preserving its full Hamilton edge partition. -/
theorem normalized_eq_multiplicity {R : W→W→Prop} {m : Nat} (hB : 0<B)
    (HD : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address (k+h)→Fin m) (z : Fin 2)
    (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk hh room S ho hbalance exceptional H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=
    MersennePhysicalIncidence.multiplicity he C k h hk hh room S ho hbalance exceptional z
      (fun q=>(H (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q)).position v.2) v.1 := by
  dsimp only
  apply postflip_eq_multiplicity he C k h hk hh room S ho hbalance exceptional hB _ _ z v
  intro a
  exact (HamiltonCommonLast.last_vertex HD last (assigned true a)).trans
    (HamiltonCommonLast.last_vertex HD last (assigned false a)).symm

end Source
/-- Exceptional small-base actual postflip family count, with common H
omission derived from genuine Hamilton decomposition data. -/
theorem normalized_small {V W : Type} {B m : Nat} {R : W→W→Prop}
    (C : ClockData V (2^2)) (t h : Nat) (hh : 0<h)
    (room : 2^(t+2+h+3)∣lengthPower (2^2) (t+2))
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (t+2+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (hB : 0<B) (HD : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address (t+2+h)→Fin m) (z : Fin 2)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange (2^(t+2+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet (by omega) C (t+2) h (by omega) hh room S ho hbalance true H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=2^(t+2+h)-1 := by
  dsimp only
  rw [normalized_eq_multiplicity]
  exact MersennePhysicalIncidence.small_multiplicity C t h hh room S ho hbalance z _ v.1

/-- Ordinary larger-base actual postflip family has exactly L−1 physical
marks at every common host point; no global cover/count premise. -/
theorem normalized_large {V W : Type} {e B m : Nat} {R : W→W→Prop}
    (he : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k) (hh : 0<h)
    (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (hB : 0<B) (HD : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address (k+h)→Fin m) (z : Fin 2)
    (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet (by omega) C k h hk hh room S ho hbalance false H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=2^(k+h)-1 := by
  dsimp only
  rw [normalized_eq_multiplicity]
  exact MersennePhysicalIncidence.large_multiplicity he C k h hk hh room S ho hbalance z _ v.1

#print axioms normalized_small
#print axioms normalized_large
#print axioms true_clock
#print axioms pair_preservation
#print axioms normalized_eq_multiplicity
end ErdePaths.MersenneReciprocalMulticover
