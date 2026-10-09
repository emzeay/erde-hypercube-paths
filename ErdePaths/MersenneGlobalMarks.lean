import ErdePaths.MersenneChronologicalMarks
import ErdePaths.SourceGlobalMarks

namespace ErdePaths.MersenneGlobalMarks
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts
open SquareLift AACTransition AACFine AACFineClock AACMarkIntervals
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

private theorem long_seams {e : Nat} (he : 2≤e) (k h : Nat) (hk : 2≤k) :
    let K := 2^(e*2^(k+h+1)-1)
    let t : Fin K→Bool := TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
      (TurnPatterns.long (P:=2^(k+h+1)))
    t ⟨0,Nat.two_pow_pos _⟩=false ∧
    t ⟨1,by have := SourceLengths.coarse_size he k h 1 (by omega); omega⟩=false ∧
    t (predecessor (Nat.two_pow_pos _) ⟨0,Nat.two_pow_pos _⟩)=true := by
  have hp : 8≤2^(k+h+1) := Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)
  dsimp only
  constructor
  · rw [TurnPatterns.repeated_zero]; exact TurnPatterns.long_zero hp
  constructor
  · unfold TurnPatterns.repeated
    have ht : (⟨1%(2*2^(k+h+1)),Nat.mod_lt _ (Nat.mul_pos (by decide) (Nat.two_pow_pos _))⟩ : Fin (2*2^(k+h+1)))=
        ⟨1,by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [ht]; exact TurnPatterns.long_one hp
  · have hs : predecessor (Nat.two_pow_pos _) (⟨0,Nat.two_pow_pos _⟩ : Fin (2^(e*2^(k+h+1)-1)))=
        ⟨2^(e*2^(k+h+1)-1)-1,by have := Nat.two_pow_pos (e*2^(k+h+1)-1); omega⟩ := by
      apply Fin.ext
      simp [predecessor,Nat.mod_eq_of_lt (show 2^(e*2^(k+h+1)-1)-1<2^(e*2^(k+h+1)-1) by
        have := Nat.two_pow_pos (e*2^(k+h+1)-1); omega)]
    rw [hs,TurnPatterns.repeated_last _ (Nat.two_pow_pos _) (coarse_div he k h)]
    exact TurnPatterns.long_last hp

/-- Every literal long-pattern chronological word contains at least one
surviving distinct mark in every H row. -/
theorem word_length {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (exceptional : Bool) (z : Fin 2) (hz : 0<z.val)
    (hB : 0<B) (hB4 : 4≤B) (hb : B%2=0)
    (H : Bool→Address (k+h)→ClockData W B) (q : Vertex (k+h+1)) :
    4≤(MersenneChronologicalMarks.word he C k h hk hh room S ho hbalance exceptional z hB H q).length := by
  have hK := SourceLengths.coarse_size he k h 1 (show 1<k+h+1 by omega)
  have hs := long_seams he k h hk
  let E := MersenneChronologicalMarks.sourceEuler he k h hk hB
  have hl := SourceMarkSize.length_ge_rows (show 1<2^(e*2^(k+h+1)-1) by omega)
    (by decide : 0<2) hB _ hs.1 hs.2.1 hs.2.2 (B-1) hb E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) E.surjective z hz
  unfold MersenneChronologicalMarks.word
  dsimp only
  rw [List.length_map]
  exact Nat.le_trans hB4 hl

abbrev Physical := SourceGlobalMarks.Physical

section Small
variable {d m M B : Nat}
variable (D : HamiltonData.DecompositionData (Vertex 2) (@Adjacent 2) m (2^2) (Nat.two_pow_pos 2))
variable (t h : Nat) (hh : 0<h) (room : 2^(t+2+h+3)∣lengthPower (2^2) (t+2))
variable (S : Fin m→Address (t+2)→Fin (2^(2*2^(t+2)))→Bool)
variable (ho : ∀f a, Profile.cardinality (S f a)%2=1)
variable (hbalance : ∀f, ∀a : Address (t+2+h), Profile.prefixCount (S f (lowerAddress a)) 2=1)
variable (hB : 0<B) (hB4 : 4≤B) (hb : B%2=0)
variable (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB)
variable (last : Vertex d) (assigned : Fin m→Bool→Address (t+2+h)→Fin M) (z : Fin 2) (hz : 0<z.val)

/-- All exceptional-base parents in literal initial-factor-major order. -/
noncomputable def small_marks : ChordGraph.Marks (Physical 2 d (t+2) h)
    (SourceChronologicalMarks.physicalParity (e:=2) (d:=d) (a:=t+2) (h:=h))
    (m*2^(t+2+h+1)) (m*(2^(t+2+h)-1)) :=
  SourceGlobalMarks.aggregate (Nat.two_pow_pos _) (fun f=>
    MersenneChronologicalMarks.small_marks D t h hh room S ho hbalance hB (by omega) hb
      HD last (assigned f) z hz f)

theorem small_word_lookup (f : Fin m) (q : Fin (2^(t+2+h+1))) :
    (small_marks D t h hh room S ho hbalance hB hB4 hb HD last assigned z hz).word
      (AnchoredEmbedding.positionEncode f q)=
    MersenneChronologicalMarks.word (by omega) (D.cycles f).toClockData (t+2) h (by omega) hh room
      (S f) (ho f) (hbalance f) true z hB
      (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned f eps a)).toClockData) q :=
  SourceGlobalMarks.aggregate_word (Nat.two_pow_pos _) _ f q

theorem small_word_length (n : Fin (m*2^(t+2+h+1))) :
    4≤((small_marks D t h hh room S ho hbalance hB hB4 hb HD last assigned z hz).word n).length := by
  let p := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (t+2+h+1)) n
  exact word_length (by omega) (D.cycles p.1).toClockData (t+2) h (by omega) hh room
    (S p.1) (ho p.1) (hbalance p.1) true z hz hB hB4 hb
    (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned p.1 eps a)).toClockData) p.2

theorem small_exists_schedule : Nonempty (MarkSchedule.Data
    (small_marks D t h hh room S ho hbalance hB hB4 hb HD last assigned z hz)) :=
  MarkSchedule.exists_data (SourceGlobalMarks.enumeration 2 d (t+2) h)
    (small_marks D t h hh room S ho hbalance hB hB4 hb HD last assigned z hz)
    (small_word_length D t h hh room S ho hbalance hB hB4 hb HD last assigned z hz)

noncomputable def small_schedule : MarkSchedule.Data
    (small_marks D t h hh room S ho hbalance hB hB4 hb HD last assigned z hz) :=
  Classical.choice (small_exists_schedule D t h hh room S ho hbalance hB hB4 hb HD last assigned z hz)
end Small

section Large
variable {e d m M B : Nat}
variable (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
variable (he : 4≤e) (k h : Nat) (hk : 2≤k) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
variable (S : Fin m→Address k→Fin (2^(e*2^k))→Bool)
variable (ho : ∀f a, Profile.cardinality (S f a)%2=1)
variable (hbalance : ∀f, ∀a : Address (k+h), Profile.prefixCount (S f (lowerAddress a)) 2=1)
variable (hB : 0<B) (hB4 : 4≤B) (hb : B%2=0)
variable (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB)
variable (last : Vertex d) (assigned : Fin m→Bool→Address (k+h)→Fin M) (z : Fin 2) (hz : 0<z.val)

/-- Ordinary larger-base parents with exact degree m*(L−1). -/
noncomputable def large_marks : ChordGraph.Marks (Physical e d k h)
    (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=k) (h:=h))
    (m*2^(k+h+1)) (m*(2^(k+h)-1)) :=
  SourceGlobalMarks.aggregate (Nat.two_pow_pos _) (fun f=>
    MersenneChronologicalMarks.large_marks D he k h hk hh room S ho hbalance hB (by omega) hb
      HD last (assigned f) z hz f)

theorem large_word_lookup (f : Fin m) (q : Fin (2^(k+h+1))) :
    (large_marks D he k h hk hh room S ho hbalance hB hB4 hb HD last assigned z hz).word
      (AnchoredEmbedding.positionEncode f q)=
    MersenneChronologicalMarks.word (by omega) (D.cycles f).toClockData k h hk hh room
      (S f) (ho f) (hbalance f) false z hB
      (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned f eps a)).toClockData) q :=
  SourceGlobalMarks.aggregate_word (Nat.two_pow_pos _) _ f q

theorem large_word_length (n : Fin (m*2^(k+h+1))) :
    4≤((large_marks D he k h hk hh room S ho hbalance hB hB4 hb HD last assigned z hz).word n).length := by
  let p := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (k+h+1)) n
  exact word_length (by omega) (D.cycles p.1).toClockData k h hk hh room
    (S p.1) (ho p.1) (hbalance p.1) false z hz hB hB4 hb
    (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned p.1 eps a)).toClockData) p.2

theorem large_exists_schedule : Nonempty (MarkSchedule.Data
    (large_marks D he k h hk hh room S ho hbalance hB hB4 hb HD last assigned z hz)) :=
  MarkSchedule.exists_data (SourceGlobalMarks.enumeration e d k h)
    (large_marks D he k h hk hh room S ho hbalance hB hB4 hb HD last assigned z hz)
    (large_word_length D he k h hk hh room S ho hbalance hB hB4 hb HD last assigned z hz)

noncomputable def large_schedule : MarkSchedule.Data
    (large_marks D he k h hk hh room S ho hbalance hB hB4 hb HD last assigned z hz) :=
  Classical.choice (large_exists_schedule D he k h hk hh room S ho hbalance hB hB4 hb HD last assigned z hz)
end Large

/-- Actual source-factor lookup of the parent/configuration word; the
numeric index is the same mixed-radix enumeration as both aggregations. -/
def sourceIndex {m : Nat} (k h : Nat) (n : Fin (m*2^(k+h+1))) :
    Fin (HamiltonTower.count (2*HamiltonTower.count m k) h) :=
  SourceGlobalMarks.sourceIndex k h 1 n

theorem sourceIndex_lookup {m : Nat} (k h : Nat) (f : Fin m) (q : Fin (2^(k+h+1))) :
    sourceIndex k h (AnchoredEmbedding.positionEncode f q)=
      SourceFactors.index k h f (epsilonOf 1 q) (addressOf 1 q) :=
  SourceGlobalMarks.sourceIndex_lookup k h 1 f q

theorem sourceIndex_injective {m : Nat} (k h : Nat) (hk : 2≤k) :
    Function.Injective (@sourceIndex m k h) :=
  SourceGlobalMarks.sourceIndex_injective k h 1 (by omega)

theorem sourceIndex_surjective {m : Nat} (k h : Nat) (hk : 2≤k) :
    Function.Surjective (@sourceIndex m k h) :=
  SourceGlobalMarks.sourceIndex_surjective k h 1 (by omega)

#print axioms sourceIndex_injective
#print axioms sourceIndex_surjective
#print axioms word_length
#print axioms small_marks
#print axioms small_word_lookup
#print axioms small_word_length
#print axioms small_schedule
#print axioms large_marks
#print axioms large_word_lookup
#print axioms large_word_length
#print axioms large_schedule
end ErdePaths.MersenneGlobalMarks
