import ErdePaths.QuarterPhysicalIncidence
import ErdePaths.QuarterSourceOrigins
import ErdePaths.SourceReciprocalExchange
import ErdePaths.DenseCodePairs
import ErdePaths.HamiltonCommonLast
import ErdePaths.SourceMarkMulticover

namespace ErdePaths.QuarterReciprocalMulticover
open SourceClock SourceProfile HierarchicalDecode SquareLift PairedArc QuarterProfileOrigins
attribute [local instance] Classical.propDecidable
private theorem indicator_sum {X : Type} (p : X→Bool) (l : List X) :
    (l.map (fun x => if p x then 1 else 0)).sum=l.countP p := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons,List.sum_cons,List.countP_cons,ih]; omega

private theorem count_unique {X : Type} [DecidableEq X] (l : List X) (hn : l.Nodup)
    (p : X→Bool) (owner : X) (hp : ∀ x∈l, p x=true ↔ x=owner) :
    l.countP p=if owner∈l then 1 else 0 := by
  classical
  have hc : l.countP p=l.count owner := by
    apply List.countP_congr
    intro x hx
    simpa only [beq_iff_eq] using hp x hx
  exact hc.trans hn.count

section Actual
variable {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
local notation "K" => QuarterPhysicalIncidence.K e
local notation "hN" => Nat.mul_pos (Nat.two_pow_pos (e*2^2-1)) (by decide : 0<2)

noncomputable def arc (epsilon : Bool) (a : Address 1) :
    DirectedArc hN (QuarterPhysicalIncidence.raw he C epsilon a) 2 := by
  exact SourceReciprocalExchange.castArc (QuarterPhysicalIncidence.length_eq he) (show 2=2 from rfl)
    _ hN _ (QuarterProfileOrigins.arc he C epsilon a)

theorem arc_zero (eps : Bool) (a : Address 1) :
    (arc he C eps a).vertex ⟨0,by decide⟩=(QuarterProfileOrigins.arc he C eps a).vertex ⟨0,by decide⟩ :=
  SourceReciprocalExchange.castArc_zero (QuarterPhysicalIncidence.length_eq he) (show 2=2 from rfl)
    _ hN _ (QuarterProfileOrigins.arc he C eps a)

theorem arc_last (eps : Bool) (a : Address 1) :
    (arc he C eps a).vertex ⟨2,by decide⟩=(QuarterProfileOrigins.arc he C eps a).vertex ⟨2,by decide⟩ :=
  SourceReciprocalExchange.castArc_last (QuarterPhysicalIncidence.length_eq he) (show 2=2 from rfl)
    _ hN _ (QuarterProfileOrigins.arc he C eps a)

theorem start_equal (a : Address 1) : (arc he C false a).vertex ⟨0,by decide⟩=(arc he C true a).vertex ⟨0,by decide⟩ := by
  rw [arc_zero,arc_zero]
  exact (QuarterSourceOrigins.data he C a).start_equal

theorem end_equal (a : Address 1) : (arc he C false a).vertex ⟨2,by decide⟩=(arc he C true a).vertex ⟨2,by decide⟩ := by
  rw [arc_last,arc_last]
  exact (QuarterSourceOrigins.data he C a).end_equal

theorem position_eq (eps : Bool) (a : Address 1) (v : VertexPower V 1×VertexPower V 1) :
    (QuarterPhysicalIncidence.raw he C eps a).position v=
    Fin.cast (QuarterPhysicalIncidence.length_eq he) ((QuarterProfileOrigins.clock he C eps a).position v) := by
  apply Fin.ext
  exact QuarterPhysicalIncidence.raw_position he C eps a v

theorem true_clock (a : Address 1) : QuarterPhysicalIncidence.oriented he C true a=
    ReciprocalEndpoints.forwardClock hN (QuarterPhysicalIncidence.raw he C true a) (arc he C true a)
      (BaselinePhysical.threshold (Nat.two_pow_pos _) (⟨1,by decide⟩ : Fin 2)) := by
  unfold ReciprocalEndpoints.forwardClock
  rw [arc_last]
  have hh := position_eq he C true a ((QuarterProfileOrigins.arc he C true a).vertex ⟨2,by decide⟩)
  exact congrArg (fun p : Fin (K*2)=>OrientedClock.clock hN (QuarterPhysicalIncidence.raw he C true a)
    (backward hN p (BaselinePhysical.threshold (Nat.two_pow_pos _) (⟨1,by decide⟩ : Fin 2))) true) hh.symm

theorem false_clock (a : Address 1) : QuarterPhysicalIncidence.oriented he C false a=
    ReciprocalEndpoints.reverseClock hN (QuarterPhysicalIncidence.raw he C false a) (arc he C false a)
      (BaselinePhysical.threshold (Nat.two_pow_pos _) (⟨1,by decide⟩ : Fin 2)) := by
  unfold ReciprocalEndpoints.reverseClock
  rw [arc_zero]
  have hh := position_eq he C false a ((QuarterProfileOrigins.arc he C false a).vertex ⟨0,by decide⟩)
  exact congrArg (fun p : Fin (K*2)=>OrientedClock.clock hN (QuarterPhysicalIncidence.raw he C false a)
    (forward hN p (BaselinePhysical.threshold (Nat.two_pow_pos _) (⟨1,by decide⟩ : Fin 2))) false) hh.symm

noncomputable def markSet (H : Bool→Address 1→ClockData W B) (post epsilon : Bool) (a : Address 1)
    (v : (VertexPower V 1×VertexPower V 1)×W) : Prop :=
  AACMarkExchange.ImageSet (ReciprocalEndpoints.host (QuarterPhysicalIncidence.oriented he C epsilon a) (H epsilon a))
    (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (if post then AACInduction.turnsAfter (Nat.two_pow_pos _)
      QuarterPatternGeometry.quarter (B-1) else fun w=>QuarterPatternGeometry.quarter w.1)
      (⟨1,by decide⟩ : Fin 2)) v

theorem pair_preservation (hB : 0<B) (H : Bool→Address 1→ClockData W B) (a : Address 1)
    (hlast : (H true a).cycle ⟨B-1,by omega⟩=(H false a).cycle ⟨B-1,by omega⟩)
    (v : (VertexPower V 1×VertexPower V 1)×W) :
    AACMarkExchange.incidence (markSet he C H true true a v)+AACMarkExchange.incidence (markSet he C H true false a v)=
    AACMarkExchange.incidence (markSet he C H false true a v)+AACMarkExchange.incidence (markSet he C H false false a v) := by
  dsimp only [markSet]
  rw [true_clock,false_clock,SourceReciprocalExchange.threshold_eq]
  have hk4 : 4≤K := Nat.le_of_dvd (Nat.two_pow_pos _) (QuarterPhysicalIncidence.period he)
  have hs := SourceReciprocalExchange.anti_seams (by omega : 1<K) (by decide : 0<2)
    (by decide : 2%2=0) (by decide : 1<2) (by decide : 1%2=1) (QuarterPhysicalIncidence.period he)
  exact ReciprocalEndpoints.preservation (by omega : 1<K) (by decide) hB _ _
    (arc he C true a) (arc he C false a) (start_equal he C a).symm (end_equal he C a).symm
    (H true a) (H false a) hlast (⟨1,by decide⟩ : Fin 2) _ _ hs.1 hs.2.1 hs.2.2 hs.1 hs.2.1 hs.2.2 v

theorem baseline_iff (H : Bool→Address 1→ClockData W B) (epsilon : Bool) (a : Address 1)
    (v : (VertexPower V 1×VertexPower V 1)×W) :
    markSet he C H false epsilon a v ↔
      ((QuarterProfileOrigins.clock he C epsilon a).position v.1).val%4=code epsilon a := by
  unfold markSet
  simp only [Bool.false_eq_true,ite_false,SourceMarkMulticover.host_image_iff]
  exact QuarterPhysicalIncidence.baseline_iff he C epsilon a v.1 ((H epsilon a).position v.2)

theorem baseline_count (H : Bool→Address 1→ClockData W B)
    (v : (VertexPower V 1×VertexPower V 1)×W) :
    ((List.finRange 4).map (fun q=>AACMarkExchange.incidence (markSet he C H false
      (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) v))).sum=1 := by
  obtain ⟨eps,a,ha,hu⟩ := unique_quarter_owner he C v.1
  let owner : Vertex 2 := DenseSourceMarks.code 1 (by decide) eps a
  have hp (q : Vertex 2) : markSet he C H false (DenseSourceCounts.epsilonOf 1 q)
      (DenseSourceCounts.addressOf 1 q) v ↔ q=owner := by
    rw [baseline_iff]
    constructor
    · intro hh
      obtain ⟨heps,had⟩ := hu _ _ hh
      rw [←DenseSourceCounts.code_of 1 (by decide) q,heps,had]
    · intro hh
      subst q
      simpa only [owner,DenseSourceCounts.epsilon_of_code,DenseSourceCounts.address_of_code] using ha
  have hf : (fun q : Vertex 2=>AACMarkExchange.incidence (markSet he C H false
      (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) v))=
      (fun q=>if q=owner then 1 else 0) := by
    funext q
    simp only [AACMarkExchange.incidence,hp]
  rw [hf]
  have hs := indicator_sum (fun q : Vertex 2=>decide (q=owner)) (List.finRange 4)
  simp only [decide_eq_true_eq] at hs
  rw [hs]
  simpa only [List.mem_finRange,ite_true] using count_unique (List.finRange 4)
    (List.nodup_finRange _) (fun q : Vertex 2=>decide (q=owner)) owner (by intro q hq; simp)

theorem postflip_count (hB : 0<B) (H : Bool→Address 1→ClockData W B)
    (hlast : ∀a,(H true a).cycle ⟨B-1,by omega⟩=(H false a).cycle ⟨B-1,by omega⟩)
    (v : (VertexPower V 1×VertexPower V 1)×W) :
    ((List.finRange 4).map (fun q=>AACMarkExchange.incidence (markSet he C H true
      (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) v))).sum=1 := by
  have hx := DenseCodePairs.aggregate_exchange 1 (by decide : 1<1+1)
    (fun eps a=>AACMarkExchange.incidence (markSet he C H true eps a v))
    (fun eps a=>AACMarkExchange.incidence (markSet he C H false eps a v))
    (fun a=>by have hh := pair_preservation he C hB H a (hlast a) v; omega)
  exact hx.trans (baseline_count he C H v)

/-- Genuine H Hamilton normalization derives the shared physical omitted
row internally, for arbitrary actual assigned H factor indices. -/
theorem normalized_count {R : W→W→Prop} {m : Nat} (hB : 0<B)
    (HD : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address 1→Fin m) (v : (VertexPower V 1×VertexPower V 1)×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange 4).map (fun q=>AACMarkExchange.incidence (markSet he C H true
      (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) v))).sum=1 := by
  dsimp only
  apply postflip_count he C hB _ _ v
  intro a
  exact (HamiltonCommonLast.last_vertex HD last (assigned true a)).trans
    (HamiltonCommonLast.last_vertex HD last (assigned false a)).symm

end Actual
#print axioms normalized_count
#print axioms postflip_count
#print axioms baseline_count
#print axioms pair_preservation
end ErdePaths.QuarterReciprocalMulticover
