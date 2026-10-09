import ErdePaths.TurnPatterns

namespace ErdePaths.BaselineResidues
open SquareLift AACTransition AACMarkIntervals AnchoredEmbedding

/-- Literal fine-coordinate residues, with the internal offset retained. -/
theorem encoded_residue {A P : Nat} (_hA : 0<A) (hP : 0<P)
    (i d : Nat) (hd : d<A) :
    (A*i+d)%(A*P)=A*(i%P)+d := by
  have hm : A*(i%P+1)≤A*P := Nat.mul_le_mul_left A
    (show i%P+1≤P by have := Nat.mod_lt i hP; omega)
  rw [Nat.mul_add,Nat.mul_one] at hm
  have hl : A*(i%P)+d<A*P := by omega
  have ha : A≤A*P := by
    have hh := Nat.mul_le_mul_left A (show 1≤P by omega)
    simpa only [Nat.mul_one] using hh
  rw [Nat.add_mod,Nat.mul_mod_mul_left,Nat.mod_eq_of_lt (show d<A*P by omega),Nat.mod_eq_of_lt hl]

theorem encoded_residue_iff {A P : Nat} (hA : 0<A) (hP : 0<P)
    (i d u z : Nat) (hd : d<A) (hz : z<A) :
    (A*i+d)%(A*P)=A*u+z ↔ i%P=u ∧ d=z := by
  rw [encoded_residue hA hP i d hd]
  constructor
  · intro he
    have hq := congrArg (fun n=>n/A) he
    have hr := congrArg (fun n=>n%A) he
    simp only [Nat.mul_add_div hA,Nat.div_eq_of_lt hd,Nat.div_eq_of_lt hz,Nat.add_zero] at hq
    simp only [Nat.mul_add_mod,Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hz] at hr
    exact ⟨hq,hr⟩
  · rintro ⟨he,rfl⟩; rw [he]

/-- Quotient/remainder alone identify every threshold point and its coarse
residue; no occurrence coverage or cyclic interval existence is assumed. -/
theorem threshold_residue_iff {K A P : Nat} (hA : 0<A) (hP : 0<P)
    (x : Fin (K*A)) (z : Fin A) (U : Nat→Prop) :
    (∃i : Fin K, x=positionEncode i z ∧ U (i.val%P)) ↔
      ∃u : Fin P, U u.val ∧ x.val%(A*P)=A*u.val+z.val := by
  constructor
  · rintro ⟨i,rfl,hi⟩
    exact ⟨⟨i.val%P,Nat.mod_lt _ hP⟩,hi,encoded_residue hA hP i.val z.val z.isLt⟩
  · rintro ⟨u,hu,he⟩
    let p := positionDecode hA x
    have hx := positionEncode_decode hA x
    have hv : A*p.1.val+p.2.val=x.val := congrArg Fin.val hx
    have hparts := (encoded_residue_iff hA hP p.1.val p.2.val u.val z.val p.2.isLt z.isLt).mp (hv ▸ he)
    have hz : p.2=z := Fin.ext hparts.2
    refine ⟨p.1,?_,?_⟩
    · rw [←hz]; exact hx.symm
    · rw [hparts.1]; exact hu

/-- Exact actual antiL baseline marks as the b residue classes counted by
the source decoder. The physical row is arbitrary and preserved. -/
theorem anti_marks_iff {K A B L b : Nat} (hK : 0<K) (hA : 0<A) (hL : 0<L)
    (hd : 2*L∣K) (hb : b<L) (he : L%2=0) (ho : b%2=1)
    (z : Fin A) (x : Fin (K*A)) (j : Fin B) :
    IsMark hK (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.anti (L:=L) b) w.1) z (x,j) ↔
      ∃u : Fin b, x.val%(A*L)=A*u.val+z.val := by
  rw [TurnPatterns.anti_marks hL hK hd hb he ho]
  have hc : (∃i : Fin K, ∃j' : Fin B, (x,j)=(positionEncode i z,j') ∧ i.val%L<b) ↔
      ∃i : Fin K, x=positionEncode i z ∧ i.val%L<b := by
    constructor
    · rintro ⟨i,j',hv,hi⟩; exact ⟨i,(Prod.mk.inj hv).1,hi⟩
    · rintro ⟨i,hx,hi⟩; exact ⟨i,j,Prod.ext hx rfl,hi⟩
  rw [hc,threshold_residue_iff hA hL x z (fun u=>u<b)]
  constructor
  · rintro ⟨u,hu,hx⟩; exact ⟨⟨u.val,hu⟩,hx⟩
  · rintro ⟨u,hx⟩; exact ⟨⟨u.val,by have := u.isLt; omega⟩,u.isLt,hx⟩

def Bad (P u : Nat) : Prop := u=P-2 ∨ u=P+2 ∨ u=P+3 ∨ u=2*P-1

theorem row_threshold_iff {K A B : Nat} (x : Fin (K*A)) (j : Fin B) (z : Fin A)
    (U : Nat→Prop) :
    (∃i : Fin K, ∃j' : Fin B, (x,j)=(positionEncode i z,j') ∧ U i.val) ↔
      ∃i : Fin K, x=positionEncode i z ∧ U i.val := by
  constructor
  · rintro ⟨i,j',hv,hi⟩; exact ⟨i,(Prod.mk.inj hv).1,hi⟩
  · rintro ⟨i,hx,hi⟩; exact ⟨i,j,Prod.ext hx rfl,hi⟩

/-- Exact long-word baseline marks among all literal threshold residues. -/
theorem long_marks_iff {K A B P : Nat} (hK : 0<K) (hA : 0<A) (hP : 8≤P)
    (hd : 2*P∣K) (z : Fin A) (x : Fin (K*A)) (j : Fin B) :
    IsMark hK (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) w.1) z (x,j) ↔
      ∃u : Fin (2*P), ¬Bad P u.val ∧ x.val%(A*(2*P))=A*u.val+z.val := by
  rw [TurnPatterns.long_marks hP hK hd]
  change (∃i : Fin K, ∃j' : Fin B, (x,j)=(positionEncode i z,j') ∧ ¬Bad P (i.val%(2*P))) ↔ _
  rw [row_threshold_iff x j z (fun i=>¬Bad P (i%(2*P)))]
  exact threshold_residue_iff hA (by omega) x z (fun u=>¬Bad P u)

/-- The four unmarked long-word threshold classes, not the complement of
marks on arbitrary grid/interior vertices. Valid uniformly for A=2 too. -/
theorem long_unmark_iff {K A B P : Nat} (hK : 0<K) (hA : 0<A) (hP : 8≤P)
    (hd : 2*P∣K) (z : Fin A) (x : Fin (K*A)) (j : Fin B) :
    ((∃i : Fin K, x=positionEncode i z) ∧
      ¬IsMark hK (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) w.1) z (x,j)) ↔
      ∃u : Fin (2*P), Bad P u.val ∧ x.val%(A*(2*P))=A*u.val+z.val := by
  constructor
  · rintro ⟨⟨i,hx⟩,hn⟩
    have hb : Bad P (i.val%(2*P)) := by
      apply Classical.byContradiction
      intro hb
      apply hn
      apply (long_marks_iff hK hA hP hd z x j).mpr
      refine ⟨⟨i.val%(2*P),Nat.mod_lt _ (by omega)⟩,hb,?_⟩
      rw [hx]
      exact encoded_residue hA (by omega) i.val z.val z.isLt
    exact (threshold_residue_iff hA (by omega) x z (Bad P)).mp ⟨i,hx,hb⟩
  · intro hbad
    obtain ⟨i,hx,hb⟩ := (threshold_residue_iff hA (by omega) x z (Bad P)).mpr hbad
    refine ⟨⟨i,hx⟩,?_⟩
    intro hm
    obtain ⟨u,hu,he⟩ := (long_marks_iff hK hA hP hd z x j).mp hm
    rw [hx] at he
    have hi := (encoded_residue_iff hA (by omega) i.val z.val u.val z.val z.isLt z.isLt).mp he
    exact hu (hi.1 ▸ hb)

/-- At A=2,z=1 the actual long-word unmarks have exactly the four raw
residues used by Mersenne source counting, modulo 4P. -/
theorem long_unmark_two_iff {K B P : Nat} (hK : 0<K) (hP : 8≤P)
    (hd : 2*P∣K) (x : Fin (K*2)) (j : Fin B) :
    ((∃i : Fin K, x=positionEncode i (⟨1,by decide⟩ : Fin 2)) ∧
      ¬IsMark hK (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) w.1)
        (⟨1,by decide⟩ : Fin 2) (x,j)) ↔
      x.val%(4*P)=2*P-3 ∨ x.val%(4*P)=2*P+5 ∨
      x.val%(4*P)=2*P+7 ∨ x.val%(4*P)=4*P-1 := by
  rw [long_unmark_iff hK (by decide) hP hd]
  have he : 2*(2*P)=4*P := by omega
  rw [he]
  constructor
  · rintro ⟨u,hu,hx⟩
    rcases hu with h|h|h|h <;> simp only at hx <;> omega
  · intro h
    rcases h with h|h|h|h
    · refine ⟨⟨P-2,by omega⟩,Or.inl rfl,?_⟩; simp only; omega
    · refine ⟨⟨P+2,by omega⟩,Or.inr (Or.inl rfl),?_⟩; simp only; omega
    · refine ⟨⟨P+3,by omega⟩,Or.inr (Or.inr (Or.inl rfl)),?_⟩; simp only; omega
    · refine ⟨⟨2*P-1,by omega⟩,Or.inr (Or.inr (Or.inr rfl)),?_⟩; simp only; omega

#print axioms encoded_residue
#print axioms threshold_residue_iff
#print axioms anti_marks_iff
#print axioms long_marks_iff
#print axioms long_unmark_iff
#print axioms long_unmark_two_iff
end ErdePaths.BaselineResidues
