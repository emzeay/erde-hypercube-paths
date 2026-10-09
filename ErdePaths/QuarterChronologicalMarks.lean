import ErdePaths.QuarterFactorGeometry
import ErdePaths.QuarterReciprocalMulticover
import ErdePaths.SourceChronologicalMarks
import ErdePaths.SourceMarkSize

namespace ErdePaths.QuarterChronologicalMarks
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts SquareLift
open AACTransition AACFine AACFineClock AACMarkIntervals
attribute [local instance] Classical.propDecidable

section Word
variable {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
local notation "K" => QuarterPhysicalIncidence.K e

noncomputable def word (hB : 0<B) (H : Bool→Address 1→ClockData W B)
    (q : Vertex 2) : List ((VertexPower V 1×VertexPower V 1)×W) :=
  let E:=QuarterPatternGeometry.euler (Nat.two_pow_pos _) hB (QuarterPhysicalIncidence.period he)
  (markWord (Nat.two_pow_pos _) (by decide) hB E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) (⟨1,by decide⟩ : Fin 2)).map
      (AACFineGeometry.physical (QuarterPhysicalIncidence.oriented he C (epsilonOf 1 q) (addressOf 1 q))
        (H (epsilonOf 1 q) (addressOf 1 q)))

theorem word_incidence (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0)
    (H : Bool→Address 1→ClockData W B) (q : Vertex 2) (v : (VertexPower V 1×VertexPower V 1)×W) :
    (word he C hB H q).countP (fun w=>decide (w=v))=
      AACMarkExchange.incidence (QuarterReciprocalMulticover.markSet he C H true
        (epsilonOf 1 q) (addressOf 1 q) v) := by
  have hK4 : 4≤K := Nat.le_of_dvd (Nat.two_pow_pos _) (QuarterPhysicalIncidence.period he)
  have h3 : 3≤K*2 := by omega
  have hE2 : 2≤K*B*(2+1) := by have hm := Nat.mul_le_mul_right B hK4; omega
  let E:=QuarterPatternGeometry.euler (Nat.two_pow_pos _) hB (QuarterPhysicalIncidence.period he)
  have hc:=AACMarkWord.physical_word_incidence (Nat.two_pow_pos _) (by decide) hB h3 hB3 hb
    E.orbit E.length (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) hE2
    E.injective E.surjective (⟨1,by decide⟩ : Fin 2) (by decide)
    (QuarterPhysicalIncidence.oriented he C (epsilonOf 1 q) (addressOf 1 q))
    (H (epsilonOf 1 q) (addressOf 1 q)) v
  simp only [QuarterReciprocalMulticover.markSet,ite_true,AACMarkExchange.incidence,
    SourceMarkMulticover.host_image_iff]
  refine Eq.trans ?_ hc
  apply List.countP_congr
  intro w hw
  simp only [decide_eq_true_eq]

theorem multiplicity {R : W→W→Prop} {m : Nat} (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0)
    (HD : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address 1→Fin m) (v : (VertexPower V 1×VertexPower V 1)×W) :
    let H:=fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange 4).map (fun q=>(word he C hB H q).countP (fun w=>decide (w=v)))).sum=1 := by
  dsimp only
  have hf:=funext (fun q=>word_incidence he C hB hB3 hb
    (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData) q v)
  rw [hf]
  exact QuarterReciprocalMulticover.normalized_count he C hB HD last assigned v

end Word

section Cube
variable {e d m B : Nat}
  (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
  (he : 2≤e)
local notation "K" => QuarterPhysicalIncidence.K e

theorem balanced (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0)
    (H : Bool→Address 1→HamiltonData.CycleData (Vertex d) (@Adjacent d) B hB)
    (f : Fin m) (q : Vertex 2) :
    NoncrossingMatch.Balanced (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=1) (h:=0))
      (word he (D.cycles f).toClockData hB (fun eps a=>(H eps a).toClockData) q) := by
  let I:=CubeHierarchy.sourceIso e 1 0
  let actual:=CubeHierarchy.transport I (OriginFactors.Quarter.factors D he (⟨1,by decide⟩ : Fin 2))
  let F:=actual.cycles (SourceFactors.index 1 0 f (epsilonOf 1 q) (addressOf 1 q))
  let G:=QuarterPhysicalIncidence.oriented he (D.cycles f).toClockData (epsilonOf 1 q) (addressOf 1 q)
  have hF (i : Fin (K*2)) : F.cycle i=I.encode (G.cycle i) := by
    have hc:=QuarterFactorGeometry.clock_eq D he f (epsilonOf 1 q) (addressOf 1 q)
    exact congrArg (fun T : ClockData _ (K*2)=>I.encode (T.cycle i)) hc
  have hK4 : 4≤K := Nat.le_of_dvd (Nat.two_pow_pos _) (QuarterPhysicalIncidence.period he)
  have h3 : 3≤K*2 := by omega
  have hE2 : 2≤K*B*(2+1) := by have hm := Nat.mul_le_mul_right B hK4; omega
  have hs:=SourceReciprocalExchange.anti_seams (by omega : 1<K) (by decide : 0<2)
    (by decide : 2%2=0) (by decide : 1<2) (by decide : 1%2=1) (QuarterPhysicalIncidence.period he)
  let E:=QuarterPatternGeometry.euler (Nat.two_pow_pos _) hB (QuarterPhysicalIncidence.period he)
  have hc:=AACPhysicalBalance.chronological_physical_balanced
    (by omega : 1<K) (by decide) hB h3 hB3 hb F (H (epsilonOf 1 q) (addressOf 1 q))
    rfl _ hs.1 hs.2.1 hs.2.2 (B-1) E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) hE2 E.injective E.surjective
    (⟨1,by decide⟩ : Fin 2) (by decide)
  have hw : (word he (D.cycles f).toClockData hB (fun eps a=>(H eps a).toClockData) q).map
      (fun v=>CubeProduct.encode (I.encode v.1,v.2))=
      (markWord (Nat.two_pow_pos _) (by decide) hB E.orbit E.length
        (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) (⟨1,by decide⟩ : Fin 2)).map
        (fun v=>CubeProduct.encode (F.cycle v.1,(H (epsilonOf 1 q) (addressOf 1 q)).cycle v.2)) := by
    unfold word
    dsimp only
    rw [List.map_map]
    congr 1
    funext v
    dsimp only [Function.comp_def,AACFineGeometry.physical]
    rw [hF]
  have hc' := (congrArg (NoncrossingMatch.Balanced CubeParity.parity) hw).mpr hc
  unfold NoncrossingMatch.Balanced at hc' ⊢
  simp only [List.countP_map,Function.comp_def] at hc'
  exact hc'

noncomputable def marks {M : Nat} (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0)
    (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB) (last : Vertex d)
    (assigned : Bool→Address 1→Fin M) (f : Fin m) :
    ChordGraph.Marks (VertexPower (VertexPower (Vertex e) 1×VertexPower (Vertex e) 1) 0×Vertex d)
      (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=1) (h:=0)) 4 1 where
  word:=word he (D.cycles f).toClockData hB
    (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData)
  balanced:=balanced D he hB hB3 hb (fun eps a=>(HamiltonCommonLast.normalize HD last).cycles (assigned eps a)) f
  multiplicity v:=by
    have hc:=multiplicity he (D.cycles f).toClockData hB hB3 hb HD last assigned v
    dsimp only at hc
    refine Eq.trans ?_ hc
    congr 1
    apply List.map_congr_left
    intro q hq
    apply List.countP_congr
    intro x hx
    simp only [decide_eq_true_eq]
    rfl

end Cube
#print axioms word_incidence
#print axioms multiplicity
#print axioms balanced
#print axioms marks
end ErdePaths.QuarterChronologicalMarks
