import ErdePaths.AACMarkIntervals

namespace ErdePaths.TurnPatterns
open SquareLift Profile AACTransition

/-- First half: b+1 zero vertices followed by alternating turns; second half complementary. -/
def antiCore (L b n : Nat) : Bool :=
  if n<L then decide ((n-b)%2=1) else !decide ((n-L-b)%2=1)

def anti {L : Nat} (b : Nat) (i : Fin (2*L)) : Bool := antiCore L b i.val

theorem anti_half {L b n : Nat} (hn : n<L) :
    antiCore L b (L+n)=!antiCore L b n := by
  simp [antiCore,show ¬ L+n<L by omega,hn]

theorem anti_zero {L b : Nat} (hL : 0<L) : anti (L:=L) b ⟨0,by omega⟩=false := by
  simp [anti,antiCore,hL]

theorem anti_last {L b : Nat} (hL : 0<L) (hb : b<L) (he : L%2=0) (ho : b%2=1) :
    anti (L:=L) b ⟨2*L-1,by omega⟩=true := by
  have h : (2*L-1-L-b)%2=0 := by omega
  simp [anti,antiCore,show ¬2*L-1<L by omega,h]

theorem anti_agreement {L b : Nat} (hL : 0<L) (hb : b<L)
    (he : L%2=0) (ho : b%2=1) (i : Fin (2*L)) :
    anti b i=anti b (successor (by omega) i) ↔ i.val%L<b := by
  have hi := i.isLt
  change antiCore L b i.val=antiCore L b ((i.val+1)%(2*L)) ↔ i.val%L<b
  by_cases h0 : i.val<L
  · by_cases h1 : i.val+1<L
    · have hm : (i.val+1)%(2*L)=i.val+1 := Nat.mod_eq_of_lt (by omega)
      have hr : i.val%L=i.val := Nat.mod_eq_of_lt h0
      simp only [hm,hr,antiCore,h0,h1,ite_true,decide_eq_decide]
      omega
    · have hx : i.val=L-1 := by omega
      have hm : (i.val+1)%(2*L)=L := by
        have hh : i.val+1=L := by omega
        rw [hh]; exact Nat.mod_eq_of_lt (by omega)
      have hz : (i.val-b)%2=0 := by omega
      have hr : i.val%L=i.val := Nat.mod_eq_of_lt h0
      simp [hm,antiCore,h0,hz,show ¬ L<L by omega,hr]
      omega
  · by_cases h1 : i.val+1<2*L
    · have hm : (i.val+1)%(2*L)=i.val+1 := Nat.mod_eq_of_lt h1
      have hr : i.val%L=i.val-L := by have := Nat.mod_eq_sub_mod (show L≤i.val by omega); rw [this]; exact Nat.mod_eq_of_lt (by omega)
      simp only [hm,hr,antiCore,h0,show ¬i.val+1<L by omega,ite_false]
      rw [show (∀x y : Bool, ((!x) = (!y)) ↔ x=y) from fun _ _ => ⟨Bool.not_inj,congrArg Bool.not⟩]
      simp only [decide_eq_decide]
      omega
    · have hx : i.val=2*L-1 := by omega
      have hm : (i.val+1)%(2*L)=0 := by
        have hh : i.val+1=2*L := by omega
        rw [hh,Nat.mod_self]
      have hz : (i.val-L-b)%2=0 := by omega
      simp [hm,antiCore,h0,hz,hL]
      have hr : i.val%L=L-1 := by
        rw [Nat.mod_eq_sub_mod (show L≤i.val by omega)]
        have hh : i.val-L=L-1 := by omega
        rw [hh]; exact Nat.mod_eq_of_lt (by omega)
      rw [hr]; omega

/-- Numeric prefix counts, used only to prove the existing `BalancedTurns` predicate. -/
def count (f : Nat→Bool) : Nat→Nat
  | 0 => 0
  | n+1 => count f n + (f n).toNat

theorem count_congr {f g : Nat→Bool} {n : Nat} (h : ∀i, i<n→f i=g i) :
    count f n=count g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [count,ih (fun i hi => h i (by omega)),h n (by omega)]

theorem count_add (f : Nat→Bool) (a b : Nat) :
    count f (a+b)=count f a+count (fun i => f (a+i)) b := by
  induction b with
  | zero => simp [count]
  | succ b ih =>
    change count f ((a+b)+1)=_
    rw [count,ih,count]
    omega

theorem prefix_numeric {N : Nat} (f : Nat→Bool) (n : Nat) (hn : n≤N) :
    prefixCount (fun i : Fin N => f i.val) n=count f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixCount,count,ih (by omega)]
    simp [indicator,show n<N by omega]

theorem balanced_of_antiperiod {L : Nat} (f : Nat→Bool)
    (h : ∀i, i<L→f (L+i)=!f i) :
    BalancedTurns (fun i : Fin (2*L) => f i.val) := by
  unfold BalancedTurns cardinality colorSet
  change prefixCount (fun i : Fin (2*L) => f i.val) (2*L)=prefixCount (fun i : Fin (2*L) => f i.val ^^ true) (2*L)
  rw [prefix_numeric f _ (by omega),prefix_numeric (fun i => f i ^^ true) _ (by omega)]
  have hn : count (fun i => f (L+i)) L=count (fun i => !f i) L :=
    count_congr h
  have hp : count (fun i => f (L+i) ^^ true) L=count f L := by
    apply count_congr
    intro i hi
    rw [h i hi]; cases f i <;> rfl
  have hq : count (fun i => f i ^^ true) L=count (fun i => !f i) L := by
    apply count_congr; intro i hi; cases f i <;> rfl
  have he : 2*L=L+L := by omega
  rw [he,count_add,count_add,hn,hp,hq]
  omega

theorem anti_balanced (L b : Nat) : BalancedTurns (anti (L:=L) b) :=
  balanced_of_antiperiod _ (fun _ hi => anti_half hi)

/-- Literal periodic repetition of a finite turn word. -/
def repeated {P K : Nat} (hP : 0<P) (t : Fin P→Bool) (i : Fin K) : Bool :=
  t ⟨i.val%P,Nat.mod_lt _ hP⟩

theorem repeated_successor {P K : Nat} (hP : 0<P) (hK : 0<K) (hd : P∣K)
    (t : Fin P→Bool) (i : Fin K) :
    repeated hP t (successor hK i)=t (successor hP ⟨i.val%P,Nat.mod_lt _ hP⟩) := by
  unfold repeated successor
  congr 1
  apply Fin.ext
  simp only [Nat.mod_mod_of_dvd _ hd,Nat.add_mod,Nat.mod_mod]

theorem periodic_count (P T : Nat) (f : Nat→Bool) (hf : ∀i, f (P+i)=f i) :
    count f (P*T)=T*count f P := by
  have hshift : ∀t i, f (P*t+i)=f i := by
    intro t; induction t with
    | zero => simp
    | succ t ih => intro i; rw [Nat.mul_succ];
                   have he : P*t+P+i=P+(P*t+i) := by omega
                   rw [he,hf,ih]
  induction T with
  | zero => simp [count]
  | succ T ih =>
    rw [Nat.mul_succ,count_add,ih]
    have hc : count (fun i => f (P*T+i)) P=count f P := count_congr (fun i _ => hshift T i)
    rw [hc,Nat.succ_mul]

theorem repeated_balanced {P K : Nat} (hP : 0<P) (hd : P∣K)
    (t : Fin P→Bool) (hb : BalancedTurns t) : BalancedTurns (repeated hP t (K:=K)) := by
  let f : Nat→Bool := fun i => t ⟨i%P,Nat.mod_lt _ hP⟩
  have hf : ∀i, f (P+i)=f i := by intro i; simp [f]
  have hnf : ∀i, (f (P+i) ^^ true)=(f i ^^ true) := fun i => congrArg (fun x => x ^^ true) (hf i)
  have he : count f P=count (fun i => f i ^^ true) P := by
    unfold BalancedTurns cardinality at hb
    rw [←prefix_numeric (N:=P) f P (by omega),←prefix_numeric (N:=P) (fun i => f i ^^ true) P (by omega)]
    have ht : (fun i : Fin P => f i.val)=t := by funext i; simp [f,Nat.mod_eq_of_lt i.isLt]
    have htc : (fun i : Fin P => f i.val ^^ true)=colorSet t true := by
      funext i; simp [f,colorSet,Nat.mod_eq_of_lt i.isLt]
    rw [ht,htc]; exact hb
  unfold BalancedTurns cardinality repeated colorSet
  change prefixCount (fun i : Fin K => f i.val) K=prefixCount (fun i : Fin K => f i.val ^^ true) K
  rw [prefix_numeric f _ (by omega),prefix_numeric (fun i => f i ^^ true) _ (by omega)]
  obtain ⟨T,rfl⟩ := hd
  rw [periodic_count P T f hf,periodic_count P T (fun i => f i ^^ true) hnf,he]

theorem repeated_anti_agreement {L b K : Nat} (hL : 0<L) (hK : 0<K)
    (hd : 2*L∣K) (hb : b<L) (he : L%2=0) (ho : b%2=1) (i : Fin K) :
    repeated (by omega) (anti (L:=L) b) i=repeated (by omega) (anti (L:=L) b) (successor hK i) ↔ i.val%L<b := by
  rw [repeated_successor (by omega) hK hd]
  change anti b ⟨i.val%(2*L),Nat.mod_lt _ (by omega)⟩ = _ ↔ _
  rw [anti_agreement hL hb he ho]
  rw [Nat.mod_mod_of_dvd _ (show L∣2*L from ⟨2,by omega⟩)]

theorem repeated_anti_balanced {L K : Nat} (hL : 0<L) (hd : 2*L∣K) (b : Nat) :
    BalancedTurns (repeated (by omega) (anti (L:=L) b) (K:=K)) :=
  repeated_balanced (by omega) hd _ (anti_balanced L b)

/-- Literal Mersenne word: 0^(P-1),1^4,0,1^(P-4). -/
def longCore (P n : Nat) : Bool := decide (P-1≤n ∧ n≠P+3)
def long {P : Nat} (i : Fin (2*P)) : Bool := longCore P i.val

theorem long_zero {P : Nat} (hP : 8≤P) : long (P:=P) ⟨0,by omega⟩=false := by
  simp [long,longCore]; omega

theorem long_last {P : Nat} (hP : 8≤P) : long (P:=P) ⟨2*P-1,by omega⟩=true := by
  simp [long,longCore]; omega

theorem long_isolated {P : Nat} (hP : 8≤P) :
    long (P:=P) ⟨P+2,by omega⟩=true ∧ long (P:=P) ⟨P+3,by omega⟩=false ∧
    long (P:=P) ⟨P+4,by omega⟩=true := by
  simp [long,longCore]; omega

theorem long_disagreement {P : Nat} (hP : 8≤P) (i : Fin (2*P)) :
    long i≠long (successor (by omega) i) ↔
      i.val=P-2 ∨ i.val=P+2 ∨ i.val=P+3 ∨ i.val=2*P-1 := by
  have hi := i.isLt
  change decide (P-1≤i.val ∧ i.val≠P+3)≠decide (P-1≤(i.val+1)%(2*P) ∧ (i.val+1)%(2*P)≠P+3) ↔ _
  by_cases hs : i.val+1<2*P
  · rw [Nat.mod_eq_of_lt hs]
    simp only [ne_eq,decide_eq_decide]; omega
  · have he : i.val+1=2*P := by omega
    rw [he,Nat.mod_self]
    simp only [ne_eq,decide_eq_decide]; omega

theorem count_constant (c : Bool) (n : Nat) : count (fun _ => c) n=n*c.toNat := by
  induction n with
  | zero => simp [count]
  | succ n ih => rw [count,ih,Nat.succ_mul]

theorem count_segment (f : Nat→Bool) (a n : Nat) (c : Bool)
    (h : ∀i, i<n→f (a+i)=c) : count (fun i => f (a+i)) n=n*c.toNat :=
  (count_congr h).trans (count_constant c n)

theorem long_count {P : Nat} (hP : 8≤P) (c : Bool) :
    count (fun i => longCore P i ^^ c) (2*P)=P := by
  let f := fun i => longCore P i ^^ c
  have h0 : ∀i, i<P-1→f i=c := by
    intro i hi; cases c <;> simp [f,longCore] <;> omega
  have h1 : ∀i, i<4→f (P-1+i)=!c := by
    intro i hi; have hh : P-1≤P-1+i ∧ P-1+i≠P+3 := by omega
    cases c <;> simp [f,longCore] <;> omega
  have h2 : ∀i, i<1→f (P+3+i)=c := by
    intro i hi; have : i=0 := by omega
    cases c <;> simp [f,longCore,this]
  have h3 : ∀i, i<P-4→f (P+4+i)=!c := by
    intro i hi; have hh : P-1≤P+4+i ∧ P+4+i≠P+3 := by omega
    cases c <;> simp [f,longCore] <;> omega
  have he : 2*P=((P-1)+4)+1+(P-4) := by omega
  change count f (2*P)=P
  rw [he,count_add,count_add,count_add]
  have hc0 : count f (P-1)=(P-1)*c.toNat := (count_congr h0).trans (count_constant c _)
  have hc1 := count_segment f (P-1) 4 (!c) h1
  have hc2 := count_segment f (P+3) 1 c h2
  have hc3 := count_segment f (P+4) (P-4) (!c) h3
  have he2 : P-1+4=P+3 := by omega
  have he3 : P+3+1=P+4 := by omega
  rw [he2,he3,hc0,hc1,hc2,hc3]
  cases c <;> simp only [Bool.toNat_false,Bool.toNat_true,Bool.not_false,Bool.not_true,Nat.mul_zero,Nat.mul_one] <;> omega

theorem long_balanced {P : Nat} (hP : 8≤P) : BalancedTurns (long (P:=P)) := by
  unfold BalancedTurns cardinality colorSet long
  change prefixCount (fun i : Fin (2*P) => longCore P i.val) (2*P)=prefixCount (fun i : Fin (2*P) => longCore P i.val ^^ true) (2*P)
  rw [prefix_numeric (longCore P) _ (by omega),prefix_numeric (fun i => longCore P i ^^ true) _ (by omega),long_count hP true]
  have hz := long_count hP false
  simpa using hz

theorem repeated_long_disagreement {P K : Nat} (hP : 8≤P) (hK : 0<K)
    (hd : 2*P∣K) (i : Fin K) :
    repeated (by omega) (long (P:=P)) i≠repeated (by omega) (long (P:=P)) (successor hK i) ↔
      i.val%(2*P)=P-2 ∨ i.val%(2*P)=P+2 ∨ i.val%(2*P)=P+3 ∨ i.val%(2*P)=2*P-1 := by
  rw [repeated_successor (by omega) hK hd]
  exact long_disagreement hP ⟨i.val%(2*P),Nat.mod_lt _ (by omega)⟩

theorem repeated_long_balanced {P K : Nat} (hP : 8≤P) (hd : 2*P∣K) :
    BalancedTurns (repeated (by omega) (long (P:=P)) (K:=K)) :=
  repeated_balanced (by omega) hd _ (long_balanced hP)

theorem last_residue {P K : Nat} (hP : 0<P) (hK : 0<K) (hd : P∣K) :
    (K-1)%P=P-1 := by
  have he : K-1+1=K := by omega
  have hm : ((K-1)%P+1)%P=0 := by
    have hh := Nat.mod_eq_zero_of_dvd hd
    rw [←he,Nat.add_mod] at hh
    simpa only [Nat.mod_mod,Nat.add_mod,Nat.mod_mod] using hh
  have hb := Nat.mod_lt (K-1) hP
  by_cases ht : (K-1)%P+1<P
  · rw [Nat.mod_eq_of_lt ht] at hm; omega
  · omega

theorem repeated_zero {P K : Nat} (hP : 0<P) (hK : 0<K) (t : Fin P→Bool) :
    repeated hP t ⟨0,hK⟩=t ⟨0,hP⟩ := by simp [repeated]

theorem repeated_last {P K : Nat} (hP : 0<P) (hK : 0<K) (hd : P∣K) (t : Fin P→Bool) :
    repeated (K:=K) hP t ⟨K-1,by omega⟩=t ⟨P-1,by omega⟩ := by
  unfold repeated
  congr 1
  apply Fin.ext
  exact last_residue hP hK hd

theorem anti_one {L b : Nat} (hL : 1<L) (hb : 1≤b) :
    anti (L:=L) b ⟨1,by omega⟩=false := by
  simp [anti,antiCore,hL,show 1-b=0 by omega]

theorem long_one {P : Nat} (hP : 8≤P) :
    long (P:=P) ⟨1,by omega⟩=false := by simp [long,longCore]; omega

/-- The repeated antiL word's literal physical fine-grid mark predicate. -/
theorem anti_marks {L b K A B : Nat} (hL : 0<L) (hK : 0<K)
    (hd : 2*L∣K) (hb : b<L) (he : L%2=0) (ho : b%2=1) (z : Fin A)
    (v : Fine K A B) :
    AACMarkIntervals.IsMark hK (fun w => repeated (by omega) (anti (L:=L) b) w.1) z v ↔
    ∃i : Fin K, ∃j : Fin B, v=(AnchoredEmbedding.positionEncode i z,j) ∧ i.val%L<b := by
  unfold AACMarkIntervals.IsMark
  constructor
  · rintro ⟨i,j,hv,hi⟩
    exact ⟨i,j,hv,(repeated_anti_agreement hL hK hd hb he ho i).mp hi⟩
  · rintro ⟨i,j,hv,hi⟩
    exact ⟨i,j,hv,(repeated_anti_agreement hL hK hd hb he ho i).mpr hi⟩

/-- Mersenne interior marks are precisely the complement of the four literal bad starts. -/
theorem long_marks {P K A B : Nat} (hP : 8≤P) (hK : 0<K)
    (hd : 2*P∣K) (z : Fin A) (v : Fine K A B) :
    AACMarkIntervals.IsMark hK (fun w => repeated (by omega) (long (P:=P)) w.1) z v ↔
    ∃i : Fin K, ∃j : Fin B, v=(AnchoredEmbedding.positionEncode i z,j) ∧
      ¬(i.val%(2*P)=P-2 ∨ i.val%(2*P)=P+2 ∨ i.val%(2*P)=P+3 ∨ i.val%(2*P)=2*P-1) := by
  unfold AACMarkIntervals.IsMark
  constructor
  · rintro ⟨i,j,hv,hi⟩
    exact ⟨i,j,hv,fun h => (repeated_long_disagreement hP hK hd i).mpr h hi⟩
  · rintro ⟨i,j,hv,hi⟩
    exact ⟨i,j,hv,Classical.byContradiction (fun h => hi ((repeated_long_disagreement hP hK hd i).mp h))⟩

#print axioms anti_agreement
#print axioms anti_balanced
#print axioms repeated_anti_agreement
#print axioms repeated_anti_balanced
#print axioms long_disagreement
#print axioms long_balanced
#print axioms repeated_long_disagreement
#print axioms repeated_long_balanced

#print axioms anti_marks
#print axioms long_marks
end ErdePaths.TurnPatterns
