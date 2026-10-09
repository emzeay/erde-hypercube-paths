import ErdePaths.TurnPatterns
import ErdePaths.AACPhysicalBalance
import ErdePaths.SourceGlobalMarks
import ErdePaths.MersenneChronologicalMarks

namespace ErdePaths.AACPatternCardinality
open SquareLift AACTransition AACFine AACFineClock AACMarkIntervals AACPhysicalBalance
attribute [local instance] Classical.propDecidable

/-- Ordinary finite counting agrees with the checked numeric recursion. -/
theorem fin_count (f : Nat→Bool) (N : Nat) :
    (List.finRange N).countP (fun i => f i.val)=TurnPatterns.count f N := by
  have ho : (List.ofFn (fun i : Fin N => f i.val)).countP id=TurnPatterns.count f N := by
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [List.ofFn_succ_last,List.countP_append]
      simp only [Fin.val_castSucc,Fin.val_last,List.countP_cons,List.countP_nil,id_eq,TurnPatterns.count]
      rw [ih]
      cases f N <;> simp
  have hm : (List.finRange N).map (fun i => f i.val)=List.ofFn (fun i : Fin N => f i.val) := by
    rw [List.finRange,List.map_ofFn]
    rfl
  rw [←hm,List.countP_map] at ho
  exact ho

private theorem threshold_count (n b : Nat) :
    TurnPatterns.count (fun i => decide (i<b)) n=min n b := by
  induction n with
  | zero => simp [TurnPatterns.count]
  | succ n ih =>
    rw [TurnPatterns.count,ih]
    by_cases hb : n<b
    · simp only [hb,decide_true,Bool.toNat_true]; omega
    · simp only [hb,decide_false,Bool.toNat_false]; omega

/-- Exact baseline row count for the literal periodic anti-L word. -/
theorem anti_row_count {K L b : Nat} (hK : 0<K) (hL : 0<L) (hd : 2*L∣K)
    (hb : b<L) (he : L%2=0) (ho : b%2=1) :
    (List.finRange K).countP (fun i => decide
      (TurnPatterns.repeated (by omega) (TurnPatterns.anti (L:=L) b) i=
       TurnPatterns.repeated (by omega) (TurnPatterns.anti (L:=L) b) (successor hK i)))=b*(K/L) := by
  have hc : (List.finRange K).countP (fun i => decide
      (TurnPatterns.repeated (by omega) (TurnPatterns.anti (L:=L) b) i=
       TurnPatterns.repeated (by omega) (TurnPatterns.anti (L:=L) b) (successor hK i)))=
      (List.finRange K).countP (fun i => decide (i.val%L<b)) := by
    apply List.countP_congr
    intro i hi
    simpa only [decide_eq_true_eq] using TurnPatterns.repeated_anti_agreement hL hK hd hb he ho i
  rw [hc,fin_count (fun i => decide (i%L<b)) K]
  have hdL : L∣K := Nat.dvd_trans (Nat.dvd_mul_left L 2) hd
  obtain ⟨T,hT⟩ := hdL
  have hp : ∀i, decide ((L+i)%L<b)=decide (i%L<b) := by intro i; simp
  have hl : TurnPatterns.count (fun i => decide (i%L<b)) L=b := by
    rw [TurnPatterns.count_congr (fun i hi => by rw [Nat.mod_eq_of_lt hi]),threshold_count,Nat.min_eq_right (Nat.le_of_lt hb)]
  rw [hT,TurnPatterns.periodic_count L T _ hp,hl]
  simp only [Nat.mul_div_cancel_left _ hL]
  exact Nat.mul_comm T b

private theorem bad_count {P : Nat} (hP : 8≤P) :
    (List.finRange (2*P)).countP (fun i => decide
      (i.val=P-2 ∨ i.val=P+2 ∨ i.val=P+3 ∨ i.val=2*P-1))=4 := by
  let bad : List (Fin (2*P)) := [⟨P-2,by omega⟩,⟨P+2,by omega⟩,⟨P+3,by omega⟩,⟨2*P-1,by omega⟩]
  have hn : bad.Nodup := by
    simp [bad,List.nodup_cons,Fin.mk.injEq]
    omega
  have hp : ((List.finRange (2*P)).filter (fun i => decide
      (i.val=P-2 ∨ i.val=P+2 ∨ i.val=P+3 ∨ i.val=2*P-1))).Perm bad := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) hn).mpr
    intro i
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,
      bad,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
  rw [List.countP_eq_length_filter,hp.length_eq]
  rfl

private theorem count_complement {X : Type} (l : List X) (p : X→Bool) :
    l.countP p+l.countP (fun x => !p x)=l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.countP_cons,List.length_cons]
    cases p x <;> simp_all <;> omega

/-- Exact baseline row count for the literal uniform long word. -/
theorem long_row_count {K P : Nat} (hK : 0<K) (hP : 8≤P) (hd : 2*P∣K) :
    (List.finRange K).countP (fun i => decide
      (TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) i=
       TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) (successor hK i)))=
      (2*P-4)*(K/(2*P)) := by
  let f : Nat→Bool := fun i => decide (¬(i%(2*P)=P-2 ∨ i%(2*P)=P+2 ∨
    i%(2*P)=P+3 ∨ i%(2*P)=2*P-1))
  have hc : (List.finRange K).countP (fun i => decide
      (TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) i=
       TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) (successor hK i)))=
      (List.finRange K).countP (fun i => f i.val) := by
    apply List.countP_congr
    intro i hi
    simp only [decide_eq_true_eq,f]
    constructor
    · intro heq hbad
      exact ((TurnPatterns.repeated_long_disagreement hP hK hd i).mpr hbad) heq
    · intro hbad
      exact Classical.byContradiction (fun hneq => hbad ((TurnPatterns.repeated_long_disagreement hP hK hd i).mp hneq))
  have hl : TurnPatterns.count f (2*P)=2*P-4 := by
    rw [←fin_count f (2*P)]
    have hcomp := count_complement (List.finRange (2*P))
      (fun i => decide (i.val=P-2 ∨ i.val=P+2 ∨ i.val=P+3 ∨ i.val=2*P-1))
    rw [bad_count hP,List.length_finRange] at hcomp
    have he : (List.finRange (2*P)).countP (fun i => f i.val)=
        (List.finRange (2*P)).countP (fun i => !decide (i.val=P-2 ∨ i.val=P+2 ∨ i.val=P+3 ∨ i.val=2*P-1)) := by
      apply List.countP_congr
      intro i hi
      simp [f,Nat.mod_eq_of_lt i.isLt]
    rw [he]
    omega
  have hf : ∀i, f (2*P+i)=f i := by intro i; simp [f]
  obtain ⟨T,hT⟩ := hd
  rw [hc,fin_count f K,hT,TurnPatterns.periodic_count (2*P) T f hf,hl]
  simp only [Nat.mul_div_cancel_left _ (show 0<2*P by omega)]
  exact Nat.mul_comm T (2*P-4)

/-- The actual merger preserves the total threshold mark count, not merely
parity or a assumed balanced-mark predicate. -/
theorem paired_length {K A B : Nat} (hK : 1<K) (hB : 0<B) (hbeven : B%2=0)
    (t : Fin K→Bool) (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true) (cutoff : Nat) (z : Fin A) :
    (pairedFineWord (by omega) hB (AACInduction.turnsAfter (by omega) t cutoff) z).length=
      ((List.finRange K).countP (fun i => decide (t i=t (successor (by omega) i))))*B := by
  let M := (List.finRange K).countP (fun i => decide (t i=t (successor (by omega) i)))
  have he : ∀j : Fin (B/2), (rowBlock (by omega) hB (AACInduction.turnsAfter (by omega) t cutoff) z j).length=2*M := by
    intro j
    rw [rowBlock,List.length_append,
      rowMarks_length hK t ht0 ht1 htlast cutoff z,
      rowMarks_length hK t ht0 ht1 htlast cutoff z]
    omega
  rw [pairedFineWord,List.length_flatMap]
  have hc := HallColor.constant_sum (List.finRange (B/2)) _ (2*M) (fun j _ => he j)
  rw [hc,List.length_finRange]
  have hb : 2*(B/2)=B := by omega
  change (2*M)*(B/2)=M*B
  rw [Nat.mul_comm 2 M,Nat.mul_assoc,hb]

/-- Exact chronological count comes from the actual fine-label bijection
and the proved permutation, with no chronological mark-count premise. -/
theorem chronological_length {K A B N E : Nat} (hK : 1<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hbeven : B%2=0)
    (t : Fin K→Bool) (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true) (cutoff : Nat) {hN : 0<N}
    (C : AACMerge.Orbit (State K B) (transition (by omega) hB (AACInduction.turnsAfter (by omega) t cutoff)) N hN)
    (hE : (indexList (A:=A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel (by omega) hA hB C hE))
    (hsur : Function.Surjective (fineLabel (by omega) hA hB C hE)) (z : Fin A) (hz : 0<z.val) :
    (markWord (by omega) hA hB C hE hpos z).length=
      ((List.finRange K).countP (fun i => decide (t i=t (successor (by omega) i))))*B := by
  rw [(chronological_perm (by omega) hA hB h3 hB3 hbeven C hE hpos hE2 hinj hsur z hz).length_eq]
  exact paired_length hK hB hbeven t ht0 ht1 htlast cutoff z

/-- Cardinality in the folding API is exactly literal filtered-position count. -/
theorem cardinality_count {E : Nat} (S : Fin E→Bool) :
    Profile.cardinality S=(List.finRange E).countP S := by
  let f : Nat→Bool := fun n => if hn : n<E then S ⟨n,hn⟩ else false
  have hf : (fun i : Fin E => f i.val)=S := by
    funext i
    simp only [f,dite_eq_left i.isLt]
  unfold Profile.cardinality
  rw [←hf,TurnPatterns.prefix_numeric f E (Nat.le_refl E),←fin_count f E]

/-- No cut or physical geometry premise is needed for this literal word /
cyclic flag cardinality identity. -/
theorem markWord_cardinality {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A:=A) C).length=E) (hpos : 0<E) (z : Fin A) :
    Profile.cardinality (cyclicFlag hpos (numericColor hK hA hB C hE z))=
      (markWord hK hA hB C hE hpos z).length := by
  rw [cardinality_count,markWord,List.length_map,markPositions,←List.countP_eq_length_filter]
  rfl

/-- Exact actual cyclic mark cardinality for every repeated anti-L AAC
Euler traversal with proved fine-label coverage. -/
theorem anti_cardinality {K A B N E L b : Nat} (hK : 1<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hbeven : B%2=0)
    (hL : 0<L) (hd : 2*L∣K) (hb : b<L) (he : L%2=0) (ho : b%2=1)
    (cutoff : Nat) {hN : 0<N}
    (C : AACMerge.Orbit (State K B) (transition (by omega) hB
      (AACInduction.turnsAfter (by omega)
        (TurnPatterns.repeated (Nat.mul_pos (by decide) hL) (TurnPatterns.anti (L:=L) b)) cutoff)) N hN)
    (hE : (indexList (A:=A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel (by omega) hA hB C hE))
    (hsur : Function.Surjective (fineLabel (by omega) hA hB C hE)) (z : Fin A) (hz : 0<z.val) :
    Profile.cardinality (cyclicFlag hpos (numericColor (by omega) hA hB C hE z))=
      b*(K/L)*B := by
  have hs := SourceReciprocalExchange.anti_seams hK hL he hb ho hd
  rw [markWord_cardinality,
    chronological_length hK hA hB h3 hB3 hbeven _ hs.1 hs.2.1 hs.2.2 cutoff C hE hpos hE2 hinj hsur z hz,
    anti_row_count (by omega) hL hd hb he ho]

/-- Actual long-word merger seam data, valid for every P>=8. -/
theorem long_seams {K P : Nat} (hK : 1<K) (hP : 8≤P) (hd : 2*P∣K) :
    let t : Fin K→Bool := TurnPatterns.repeated (show 0<2*P by omega) (TurnPatterns.long (P:=P))
    t ⟨0,by omega⟩=false ∧ t ⟨1,hK⟩=false ∧ t (predecessor (by omega) ⟨0,by omega⟩)=true := by
  dsimp only
  constructor
  · rw [TurnPatterns.repeated_zero]; exact TurnPatterns.long_zero hP
  constructor
  · unfold TurnPatterns.repeated
    have ht : (⟨1%(2*P),Nat.mod_lt _ (by omega)⟩ : Fin (2*P))=⟨1,by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [ht]
    exact TurnPatterns.long_one hP
  · have hp : predecessor (by omega) (⟨0,by omega⟩ : Fin K)=⟨K-1,by omega⟩ := by
      apply Fin.ext
      simp [predecessor,Nat.mod_eq_of_lt (show K-1<K by omega)]
    rw [hp,TurnPatterns.repeated_last _ (show 0<K by omega) hd]
    exact TurnPatterns.long_last hP

/-- Exact actual cyclic mark cardinality for every uniform long-pattern
AAC merger, without a mark-count or cyclic-cut premise. -/
theorem long_cardinality {K A B N E P : Nat} (hK : 1<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hbeven : B%2=0) (hP : 8≤P) (hd : 2*P∣K)
    (cutoff : Nat) {hN : 0<N}
    (C : AACMerge.Orbit (State K B) (transition (by omega) hB
      (AACInduction.turnsAfter (by omega)
        (TurnPatterns.repeated (show 0<2*P by omega) (TurnPatterns.long (P:=P))) cutoff)) N hN)
    (hE : (indexList (A:=A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel (by omega) hA hB C hE))
    (hsur : Function.Surjective (fineLabel (by omega) hA hB C hE)) (z : Fin A) (hz : 0<z.val) :
    Profile.cardinality (cyclicFlag hpos (numericColor (by omega) hA hB C hE z))=
      (2*P-4)*(K/(2*P))*B := by
  have hs := long_seams hK hP hd
  rw [markWord_cardinality,
    chronological_length hK hA hB h3 hB3 hbeven _ hs.1 hs.2.1 hs.2.2 cutoff C hE hpos hE2 hinj hsur z hz,
    long_row_count (by omega) hP hd]


/-- Canonical anti-L source Euler cardinality; the actual Euler construction
supplies all traversal and fine-label obligations internally. -/
theorem source_anti_cardinality {e B b : Nat} (he : 2≤e) (a h r : Nat) (hr : r<a+h+1)
    (hB : 0<B) (hB3 : 3≤B) (hbeven : B%2=0)
    (hb : b<2^(a+h+1-r)) (ho : b%2=1) (z : Fin (2^r)) (hz : 0<z.val) :
    let K := 2^(e*2^(a+h+1)-r)
    let D := SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB
    Profile.cardinality (cyclicFlag (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega))
      (numericColor (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB D.orbit D.length z))=
      b*(K/(2^(a+h+1-r)))*B := by
  dsimp only
  have hK4 := SourceLengths.coarse_size he a h r hr
  have hA := Nat.two_pow_pos r
  have h3 : 3≤2^(e*2^(a+h+1)-r)*2^r := by
    have hm := Nat.mul_le_mul_left (2^(e*2^(a+h+1)-r)) (show 1≤2^r by omega)
    simp only [Nat.mul_one] at hm
    omega
  have hE2 : 2≤2^(e*2^(a+h+1)-r)*B*(2^r+1) := by
    have hm := Nat.mul_le_mul_right B hK4
    have hm' := Nat.mul_le_mul_left (2^(e*2^(a+h+1)-r)*B) (show 1≤2^r+1 by omega)
    omega
  exact anti_cardinality (by omega) (Nat.two_pow_pos _) hB h3 hB3 hbeven
    (Nat.two_pow_pos _) (SourceLengths.coarse_period he a h r hr) hb
    (SourceLengths.block_even a h r hr) ho (B-1)
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB).orbit
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB).length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) hE2
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB).injective
    (SourceChronologicalMarks.sourceEuler (b:=b) he a h r hr hB).surjective z hz

private theorem exponent_room (t : Nat) : t+1≤2^t := by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos t; omega

private theorem long_coarse_div {e : Nat} (he : 2≤e) (k h : Nat) :
    2*2^(k+h+1)∣2^(e*2^(k+h+1)-1) := by
  have hp := exponent_room (k+h+1)
  have hm := Nat.mul_le_mul_right (2^(k+h+1)) he
  have hd : k+h+2≤e*2^(k+h+1)-1 := by omega
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.pow_dvd_pow 2 hd

/-- Canonical Mersenne long source Euler cardinality, uniform in both small
and large bases and in arbitrary hierarchy depth. -/
theorem source_long_cardinality {e B : Nat} (he : 2≤e) (k h : Nat) (hk : 2≤k)
    (hB : 0<B) (hB3 : 3≤B) (hbeven : B%2=0) (z : Fin 2) (hz : 0<z.val) :
    let K := 2^(e*2^(k+h+1)-1)
    let P := 2^(k+h+1)
    let D := MersenneChronologicalMarks.sourceEuler he k h hk hB
    Profile.cardinality (cyclicFlag (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide))
      (numericColor (Nat.two_pow_pos _) (by decide) hB D.orbit D.length z))=
      (2*P-4)*(K/(2*P))*B := by
  dsimp only
  have hK4 := SourceLengths.coarse_size he k h 1 (show 1<k+h+1 by omega)
  have h3 : 3≤2^(e*2^(k+h+1)-1)*2 := by omega
  have hE2 : 2≤2^(e*2^(k+h+1)-1)*B*(2+1) := by
    have hm := Nat.mul_le_mul_right B hK4
    omega
  have hP : 8≤2^(k+h+1) := Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)
  exact long_cardinality (by omega) (by decide) hB h3 hB3 hbeven hP
    (long_coarse_div he k h) (B-1)
    (MersenneChronologicalMarks.sourceEuler he k h hk hB).orbit
    (MersenneChronologicalMarks.sourceEuler he k h hk hB).length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) hE2
    (MersenneChronologicalMarks.sourceEuler he k h hk hB).injective
    (MersenneChronologicalMarks.sourceEuler he k h hk hB).surjective z hz

#print axioms anti_row_count
#print axioms long_row_count
#print axioms paired_length
#print axioms chronological_length
#print axioms anti_cardinality
#print axioms long_cardinality
#print axioms source_anti_cardinality
#print axioms source_long_cardinality
end ErdePaths.AACPatternCardinality
