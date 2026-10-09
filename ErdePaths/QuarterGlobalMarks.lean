import ErdePaths.QuarterChronologicalMarks
import ErdePaths.SourceGlobalMarks

namespace ErdePaths.QuarterGlobalMarks
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts SquareLift
open AACTransition AACFine AACFineClock AACMarkIntervals
attribute [local instance] Classical.propDecidable

theorem word_length {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (hB : 0<B) (hB4 : 4≤B) (hb : B%2=0) (H : Bool→Address 1→ClockData W B) (q : Vertex 2) :
    4≤(QuarterChronologicalMarks.word he C hB H q).length := by
  have hK4 : 4≤QuarterPhysicalIncidence.K e := Nat.le_of_dvd (Nat.two_pow_pos _) (QuarterPhysicalIncidence.period he)
  have hs:=SourceReciprocalExchange.anti_seams (by omega : 1<QuarterPhysicalIncidence.K e)
    (by decide : 0<2) (by decide : 2%2=0) (by decide : 1<2) (by decide : 1%2=1)
    (QuarterPhysicalIncidence.period he)
  let E:=QuarterPatternGeometry.euler (Nat.two_pow_pos _) hB (QuarterPhysicalIncidence.period he)
  have hl:=SourceMarkSize.length_ge_rows (show 1<QuarterPhysicalIncidence.K e by omega)
    (by decide : 0<2) hB _ hs.1 hs.2.1 hs.2.2 (B-1) hb E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) E.surjective
    (⟨1,by decide⟩ : Fin 2) (by decide)
  unfold QuarterChronologicalMarks.word
  dsimp only
  rw [List.length_map]
  exact Nat.le_trans hB4 hl

section Cube
variable {e d m M B : Nat}
  (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
  (he : 2≤e) (hB : 0<B) (hB4 : 4≤B) (hb : B%2=0)
  (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB)
  (last : Vertex d) (assigned : Fin m→Bool→Address 1→Fin M)

/-- Genuine global chronological words: exact multiplicity m*1. -/
noncomputable def marks : ChordGraph.Marks (SourceGlobalMarks.Physical e d 1 0)
    (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=1) (h:=0)) (m*4) (m*1) :=
  SourceGlobalMarks.aggregate (by decide : 0<4) (fun f=>
    QuarterChronologicalMarks.marks D he hB (by omega) hb HD last (assigned f) f)

theorem word_lookup (f : Fin m) (q : Fin 4) :
    (marks D he hB hB4 hb HD last assigned).word (AnchoredEmbedding.positionEncode f q)=
      QuarterChronologicalMarks.word he (D.cycles f).toClockData hB
        (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned f eps a)).toClockData) q :=
  SourceGlobalMarks.aggregate_word (by decide : 0<4) _ f q

theorem global_word_length (n : Fin (m*4)) :
    4≤((marks D he hB hB4 hb HD last assigned).word n).length := by
  let p:=AnchoredEmbedding.positionDecode (by decide : 0<4) n
  exact word_length he (D.cycles p.1).toClockData hB hB4 hb
    (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned p.1 eps a)).toClockData) p.2

noncomputable def schedule : MarkSchedule.Data (marks D he hB hB4 hb HD last assigned) :=
  Classical.choice (MarkSchedule.exists_data (SourceGlobalMarks.enumeration e d 1 0)
    (marks D he hB hB4 hb HD last assigned)
    (global_word_length D he hB hB4 hb HD last assigned))

end Cube
#print axioms marks
#print axioms schedule
#print axioms word_lookup
end ErdePaths.QuarterGlobalMarks
