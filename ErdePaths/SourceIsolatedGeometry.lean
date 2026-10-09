import ErdePaths.AACIsolatedFork
import ErdePaths.MersenneAACBase

namespace ErdePaths.SourceIsolatedGeometry
open SquareLift SourceClock AACTransition AACFine AACFineClock AACFineGeometry AACMarkIntervals
open SourceAACBase
attribute [local instance] Classical.propDecidable

def lastRow {B : Nat} (hB : 0<B) : Fin B := ⟨B-1,by omega⟩

theorem last_turn {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K→Bool) (i : Fin K) :
    AACInduction.turnsAfter hK t (B-1) (i,lastRow hB)=t i := by
  simp only [AACInduction.turnsAfter,lastRow,show ¬ B-1<B-1 by omega,and_false,ite_false]

/-- The actual anti-L word has an isolated turn at b+1 when at least two
further positions remain before its half-period seam. -/
theorem anti_isolated {L K b : Nat} (hK : 0<K) (hL : 0<L)
    (room : 2*L≤K) (hb : b≤L-3) (hL4 : 4≤L) :
    let i : Fin K := ⟨b+1,by omega⟩
    let t := TurnPatterns.repeated (Nat.mul_pos (by decide) hL) (TurnPatterns.anti (L:=L) b) (K:=K)
    t (predecessor hK i)=false ∧ t i=true ∧ t (successor hK i)=false := by
  dsimp only
  have hp : predecessor hK (⟨b+1,by omega⟩ : Fin K)=⟨b,by omega⟩ := by
    apply Fin.ext
    change (K-1+(b+1))%K=b
    rw [show K-1+(b+1)=b+K by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  have hs : successor hK (⟨b+1,by omega⟩ : Fin K)=⟨b+2,by omega⟩ := by
    apply Fin.ext
    change (b+1+1)%K=b+2
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp,hs]
  simp only [TurnPatterns.repeated,TurnPatterns.anti,TurnPatterns.antiCore,
    Nat.mod_eq_of_lt (show b<2*L by omega),Nat.mod_eq_of_lt (show b+1<2*L by omega),
    Nat.mod_eq_of_lt (show b+2<2*L by omega),
    show b<L by omega,show b+1<L by omega,show b+2<L by omega,ite_true]
  simp only [Nat.sub_self,show b+1-b=1 by omega,show b+2-b=2 by omega]
  decide

/-- The actual long Mersenne word has its isolated zero at P+3. -/
theorem long_isolated {K P : Nat} (hK : 0<K) (hP : 8≤P) (room : 2*P≤K) :
    let i : Fin K := ⟨P+3,by omega⟩
    let t := TurnPatterns.repeated (by omega : 0<2*P) (TurnPatterns.long (P:=P)) (K:=K)
    t (predecessor hK i)=true ∧ t i=false ∧ t (successor hK i)=true := by
  dsimp only
  have hp : predecessor hK (⟨P+3,by omega⟩ : Fin K)=⟨P+2,by omega⟩ := by
    apply Fin.ext
    change (K-1+(P+3))%K=P+2
    rw [show K-1+(P+3)=P+2+K by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  have hs : successor hK (⟨P+3,by omega⟩ : Fin K)=⟨P+4,by omega⟩ := by
    apply Fin.ext
    change (P+3+1)%K=P+4
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp,hs]
  simpa only [TurnPatterns.repeated,Nat.mod_eq_of_lt (show P+2<2*P by omega),
    Nat.mod_eq_of_lt (show P+3<2*P by omega),Nat.mod_eq_of_lt (show P+4<2*P by omega)]
    using TurnPatterns.long_isolated hP

/-- Literal unflipped-row isolated geometry, physically transported through
actual Hamilton coordinates. All neighbor scalar occurrences and their
uniqueness, flags and opposite colors are derived from the actual Euler data. -/
theorem physical_neighbors {U V : Type} {K B : Nat} (hK : 0<K) (hB : 0<B)
    (h3 : 3≤K*2) (hB3 : 3≤B) (hb : B%2=0)
    {t : Fin K→Bool} (E : SourceChronologicalMarks.EulerData hK (by decide : 0<2) hB t)
    (G : ClockData U (K*2)) (H : ClockData V B) (i : Fin K)
    (hbefore : t (predecessor hK i)≠t i) (hafter : t i≠t (successor hK i)) :
    let pos := Nat.mul_pos (Nat.mul_pos hK hB) (by decide : 0<2+1)
    let base := SourceAACBase.base hK (by decide : 0<2) hB E G H
    let color := numericColor hK (by decide : 0<2) hB E.orbit E.length (⟨1,by decide⟩ : Fin 2)
    ∃n m : Fin (K*B*(2+1)),
      base n=physical G H (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),lastRow hB) ∧
      base m=physical G H (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),lastRow hB) ∧
      (∀p,base p=base n→p=n) ∧ (∀p,base p=base m→p=m) ∧
      cyclicFlag pos color n=false ∧ cyclicFlag pos color m=false ∧ color n≠color m := by
  dsimp only
  have hE2 : 2≤K*B*(2+1) := by
    have hm := Nat.mul_pos hK hB
    omega
  obtain ⟨n,m,hn,hm,hnu,hmu,hnf,hmf,hcolor⟩ := AACIsolatedFork.isolated_occurrences hK hB h3 hB3 hb
    E.orbit E.length (Nat.mul_pos (Nat.mul_pos hK hB) (by decide)) hE2 E.injective E.surjective
    i (lastRow hB)
    (by simpa only [last_turn] using hbefore) (by simpa only [last_turn] using hafter)
  refine ⟨n,m,congrArg (physical G H) hn,congrArg (physical G H) hm,?_,?_,hnf,hmf,hcolor⟩
  · intro p hp
    exact hnu p (physical_injective G H hp)
  · intro p hp
    exact hmu p (physical_injective G H hp)

private theorem exponential_bound (t : Nat) : t+1≤2^t := by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos t; omega

/-- Full long-word period divides the actual coarse cube cycle length. -/
theorem long_period {e : Nat} (he : 2≤e) (k h : Nat) :
    2*2^(k+h+1)∣2^(e*2^(k+h+1)-1) := by
  have hp := exponential_bound (k+h+1)
  have hm := Nat.mul_le_mul_right (2^(k+h+1)) he
  have ht : k+h+2≤e*2^(k+h+1)-1 := by omega
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.pow_dvd_pow 2 ht

/-- Actual Mersenne source witnesses: no isolated-turn, scalar occurrence,
color or neighbor-uniqueness premise is supplied. -/
theorem mersenne_neighbors (I : MersenneAACBase.Input) (f : I.Index) :
    let K := 2^(I.e*2^(I.k+I.h+1)-1)
    let P := 2^(I.k+I.h+1)
    let i : Fin K := ⟨P+3,by
      have hd := long_period I.he I.k I.h
      have hl := Nat.le_of_dvd (Nat.two_pow_pos (I.e*2^(I.k+I.h+1)-1)) hd
      have hp : 8≤P := Nat.pow_le_pow_right (by decide : 1≤2) (show 3≤I.k+I.h+1 by have := I.hk; omega)
      omega⟩
    let G := MersenneAACBase.G I.D I.he I.k I.h I.hk I.hh I.room I.S I.ho I.balance I.exceptional I.z (I.factor f)
    let H := MersenneAACBase.H I.k I.h I.hk I.HD I.last (I.factor f)
    ∃n m : Fin I.E,
      I.originalBase f n=physical G H (AnchoredEmbedding.positionEncode (predecessor (Nat.two_pow_pos _) i) (⟨1,by decide⟩ : Fin 2),lastRow I.hB) ∧
      I.originalBase f m=physical G H (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),lastRow I.hB) ∧
      (∀p,I.originalBase f p=I.originalBase f n→p=n) ∧
      (∀p,I.originalBase f p=I.originalBase f m→p=m) ∧
      I.originalFlag n=false ∧ I.originalFlag m=false ∧ I.originalColor n≠I.originalColor m := by
  dsimp only
  let K := 2^(I.e*2^(I.k+I.h+1)-1)
  let P := 2^(I.k+I.h+1)
  have hd := long_period I.he I.k I.h
  have room : 2*P≤K := Nat.le_of_dvd (Nat.two_pow_pos _) hd
  have hP : 8≤P := Nat.pow_le_pow_right (by decide : 1≤2) (show 3≤I.k+I.h+1 by have := I.hk; omega)
  let i : Fin K := ⟨P+3,by omega⟩
  have hi := long_isolated (Nat.two_pow_pos _) hP room
  have hbefore : (TurnPatterns.repeated (by omega : 0<2*P) (TurnPatterns.long (P:=P)) (K:=K))
      (predecessor (Nat.two_pow_pos _) i)≠
      (TurnPatterns.repeated (by omega : 0<2*P) (TurnPatterns.long (P:=P)) (K:=K)) i := by
    rw [hi.1,hi.2.1]; decide
  have hafter : (TurnPatterns.repeated (by omega : 0<2*P) (TurnPatterns.long (P:=P)) (K:=K)) i≠
      (TurnPatterns.repeated (by omega : 0<2*P) (TurnPatterns.long (P:=P)) (K:=K)) (successor (Nat.two_pow_pos _) i) := by
    rw [hi.2.1,hi.2.2]; decide
  have hk4 := SourceLengths.coarse_size I.he I.k I.h 1 (by have := I.hk; omega)
  have hz : I.z=(⟨1,by decide⟩ : Fin 2) := by
    apply Fin.ext
    change I.z.val=1
    have hlo := I.hz
    have hhi := I.z.isLt
    omega
  simpa only [MersenneAACBase.Input.originalFlag,MersenneAACBase.Input.originalBase,
    MersenneAACBase.Input.originalColor,MersenneAACBase.sourceColor,MersenneAACBase.sourceBase,
    MersenneAACBase.Input.E,Nat.pow_one,cyclicFlag,hz,i,K,P] using physical_neighbors (Nat.two_pow_pos _) I.hB (by omega) (by have := I.hB4; omega) I.evenB
    (MersenneChronologicalMarks.sourceEuler I.he I.k I.h I.hk I.hB)
    (MersenneAACBase.G I.D I.he I.k I.h I.hk I.hh I.room I.S I.ho I.balance I.exceptional I.z (I.factor f))
    (MersenneAACBase.H I.k I.h I.hk I.HD I.last (I.factor f)) i hbefore hafter

/-- Actual ordinary A=2 source witnesses at column b+1 in the common last
H row. The geometric pattern and all numeric occurrences are constructed. -/
theorem ordinary_neighbors (I : SourceLocalFold.Input) (hr : I.r=1)
    (short : I.b≤2^(I.a+I.h+1-I.r)-3) (f : I.Index) :
    let K := 2^(I.e*2^(I.a+I.h+1)-I.r)
    let i : Fin K := ⟨I.b+1,by
      have hd := SourceLengths.coarse_period I.he I.a I.h I.r I.hr
      have hperiod := Nat.le_of_dvd (Nat.two_pow_pos (I.e*2^(I.a+I.h+1)-I.r)) hd
      have hs := I.short
      omega⟩
    let G := SourceAACBase.G I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA I.S I.ho I.balance I.z (I.factor f)
    let H := SourceAACBase.H I.a I.h I.r I.hr I.HD I.last (I.factor f)
    ∃n m : Fin I.E,
      I.originalBase f n=physical G H (AnchoredEmbedding.positionEncode (predecessor (Nat.two_pow_pos _) i) I.z,lastRow I.hB) ∧
      I.originalBase f m=physical G H (AnchoredEmbedding.positionEncode i I.z,lastRow I.hB) ∧
      (∀p,I.originalBase f p=I.originalBase f n→p=n) ∧
      (∀p,I.originalBase f p=I.originalBase f m→p=m) ∧
      I.originalFlag n=false ∧ I.originalFlag m=false ∧ I.originalColor n≠I.originalColor m := by
  cases I with
  | mk e d m u B b a h r hB he hr0 hh room hA D S ho balance HD last z hz hB4 evenB short0 odd =>
    dsimp only at hr
    subst r
    have hzone : z=(⟨1,by decide⟩ : Fin (2^1)) := by
      apply Fin.ext
      change z.val=1
      have hzlt := z.isLt
      change z.val<2 at hzlt
      omega
    subst z
    let I : SourceLocalFold.Input := ⟨e,d,m,u,B,b,a,h,1,hB,he,hr0,hh,room,hA,D,S,ho,balance,HD,last,⟨1,by decide⟩,hz,hB4,evenB,short0,odd⟩
    have hr : I.r=1 := rfl
    dsimp only
    have hr' : 1<I.a+I.h+1 := by have := I.hr; omega
    let K := 2^(I.e*2^(I.a+I.h+1)-1)
    let L := 2^(I.a+I.h+1-1)
    have hd := SourceLengths.coarse_period I.he I.a I.h 1 hr'
    have room : 2*L≤K := Nat.le_of_dvd (Nat.two_pow_pos _) hd
    have hs : I.b≤L-3 := by simpa only [hr] using short
    have hL4 : 4≤L := by have := I.odd; omega
    let i : Fin K := ⟨I.b+1,by have := I.short; omega⟩
    have hi := anti_isolated (Nat.two_pow_pos _) (Nat.two_pow_pos _) room hs hL4
    have hbefore : (TurnPatterns.repeated (by omega : 0<2*L) (TurnPatterns.anti (L:=L) I.b) (K:=K))
        (predecessor (Nat.two_pow_pos _) i)≠
        (TurnPatterns.repeated (by omega : 0<2*L) (TurnPatterns.anti (L:=L) I.b) (K:=K)) i := by
      rw [hi.1,hi.2.1]; decide
    have hafter : (TurnPatterns.repeated (by omega : 0<2*L) (TurnPatterns.anti (L:=L) I.b) (K:=K)) i≠
        (TurnPatterns.repeated (by omega : 0<2*L) (TurnPatterns.anti (L:=L) I.b) (K:=K)) (successor (Nat.two_pow_pos _) i) := by
      rw [hi.2.1,hi.2.2]; decide
    have hk4 := SourceLengths.coarse_size I.he I.a I.h 1 hr'
    have hA : 2*I.u=2^1 := by simpa only [hr] using I.hA
    have hz : I.z.val=1 := by have hh := I.hz; have hi := I.z.isLt; simp only [hr,Nat.pow_one] at hi; omega
    have hp := physical_neighbors (Nat.two_pow_pos _) I.hB (by omega) (by have := I.hB4; omega) I.evenB
      (SourceChronologicalMarks.sourceEuler (b:=I.b) I.he I.a I.h 1 hr' I.hB)
      (SourceAACBase.G I.D I.he I.a I.h 1 hr' I.hh I.room hA I.S I.ho I.balance (⟨1,by decide⟩ : Fin 2) (I.factor f))
      (SourceAACBase.H I.a I.h 1 hr' I.HD I.last (I.factor f)) i hbefore hafter
    exact hp

#print axioms anti_isolated
#print axioms long_isolated
#print axioms physical_neighbors
#print axioms mersenne_neighbors
#print axioms ordinary_neighbors
end ErdePaths.SourceIsolatedGeometry
