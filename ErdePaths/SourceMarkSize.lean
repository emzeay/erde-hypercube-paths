import ErdePaths.SourceChronologicalMarks
import ErdePaths.FiniteSaturation

namespace ErdePaths.SourceMarkSize
open SquareLift AACTransition AACFine AACFineClock AACMarkIntervals SourceClock

/-- One actual postflip mark in every row, using the surviving zero or the
new predecessor mark according to the literal merger cutoff. -/
def rowPoint {K A B : Nat} (hK : 0<K) (cutoff : Nat) (z : Fin A) (j : Fin B) : Fine K A B :=
  (AnchoredEmbedding.positionEncode
    (if j.val<cutoff then predecessor hK ⟨0,hK⟩ else ⟨0,hK⟩) z,j)

theorem rowPoint_mark {K A B : Nat} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (cutoff : Nat) (z : Fin A) (j : Fin B) :
    IsMark (by omega) (AACInduction.turnsAfter (by omega) t cutoff) z
      (rowPoint (by omega) cutoff z j) := by
  unfold rowPoint
  by_cases hj : j.val<cutoff
  · rw [ite_eq_left hj,AACMarkExchange.mark_point_iff,
      AACMarkExchange.agreement_after hK t ht0 ht1 htlast]
    exact Or.inr ⟨rfl,hj⟩
  · rw [ite_eq_right hj,AACMarkExchange.mark_point_iff,
      AACMarkExchange.agreement_after hK t ht0 ht1 htlast]
    refine Or.inl ⟨?_,?_⟩
    · rw [AACMarkExchange.successor_zero hK,ht0,ht1]
    · exact fun hh=>hj hh.2

/-- A genuine chronological Euler mark word has at least one distinct mark
per physical row; no positive mark-size premise is supplied. -/
theorem length_ge_rows {K A B N E : Nat} (hK : 1<K) (hA : 0<A) (hB : 0<B)
    (t : Fin K→Bool) (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true) (cutoff : Nat)
    (hbeven : B%2=0) {hN : 0<N}
    (C : AACMerge.Orbit (State K B) (transition (by omega) hB (AACInduction.turnsAfter (by omega) t cutoff)) N hN)
    (hE : (indexList (A:=A) C).length=E) (hpos : 0<E)
    (hsur : Function.Surjective (fineLabel (by omega) hA hB C hE)) (z : Fin A) (hz : 0<z.val) :
    B≤(markWord (by omega) hA hB C hE hpos z).length := by
  let points := List.ofFn (rowPoint (K:=K) (A:=A) (B:=B) (by omega) cutoff z)
  have hn : points.Nodup := FiniteSaturation.ofFn_nodup _ (fun i j he=>congrArg Prod.snd he)
  have hs : points ⊆ markWord (by omega) hA hB C hE hpos z := by
    intro v hv
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hv
    rw [←hj]
    exact (AACMarkWord.mem_word_iff (by omega) hA hB hbeven C hE hpos hsur z hz _).mpr
      (rowPoint_mark hK t ht0 ht1 htlast cutoff z j)
  have hh := hn.length_le_of_subset hs
  simpa only [points,List.length_ofFn] using hh

/-- Canonical actual source words have enough occurrences for a passive
noncrossing pair whenever B>=4. -/
theorem source_word_length {V W : Type} {e u B b : Nat}
    (he : 2≤e) (C : ClockData V (2^e)) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
    (S : HierarchicalDecode.Address a→Fin (2^(e*2^a))→Bool)
    (ho : ∀address, Profile.cardinality (S address)%2=1)
    (hbalance : ∀address : HierarchicalDecode.Address (a+h),
      Profile.prefixCount (S (SourceProfile.lowerAddress address)) (2*u)=u)
    (z : Fin (2^r)) (hz : 0<z.val) (hB : 0<B) (hB4 : 4≤B) (hbeven : B%2=0)
    (H : Bool→HierarchicalDecode.Address (a+h)→ClockData W B)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1) (q : Fin (2^(a+h+1))) :
    4≤(SourceChronologicalMarks.word (b:=b) he C a h r hr hh room hA S ho hbalance z hB H q).length := by
  have hK := SourceLengths.coarse_size he a h r hr
  have hs := SourceReciprocalExchange.anti_seams (show 1<2^(e*2^(a+h+1)-r) by omega)
    (Nat.two_pow_pos (a+h+1-r)) (SourceLengths.block_even a h r hr) hb hodd
    (SourceLengths.coarse_period he a h r hr)
  let E := SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB
  have hlen := length_ge_rows (by omega) (Nat.two_pow_pos r) hB _
    hs.1 hs.2.1 hs.2.2 (B-1) hbeven E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) E.surjective z hz
  unfold SourceChronologicalMarks.word
  dsimp only
  rw [List.length_map]
  exact Nat.le_trans hB4 hlen

#print axioms source_word_length
#print axioms length_ge_rows
end ErdePaths.SourceMarkSize
