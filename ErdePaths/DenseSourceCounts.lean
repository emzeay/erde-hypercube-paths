import ErdePaths.DenseSourceMarks

namespace ErdePaths.DenseSourceCounts
attribute [local instance] Classical.propDecidable
open SourceClock SourceProfile SourceStability HierarchicalDecode DenseSourceMarks

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

/-- Each canonical physical mark list contains a marked vertex once, and an
unmarked vertex zero times: actual tour injectivity excludes duplicate visits. -/
theorem marked_list_count {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (u : Nat)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (markedVertices he C k h r hr S ho direction epsilon address u).countP (fun w => decide (w=v))=
      if Marked he C k h r hr S ho direction epsilon address u v then 1 else 0 := by
  classical
  rw [markedVertices,List.countP_map,List.countP_filter]
  let T := clock he C k h S ho epsilon address
  by_cases hm : Marked he C k h r hr S ho direction epsilon address u v
  · rw [ite_eq_left hm]
    have hc := count_unique (List.finRange _) (List.nodup_finRange _)
      (fun t => decide (T.cycle t=v) && decide (Marked he C k h r hr S ho direction epsilon address u (T.cycle t)))
      (T.position v) (by
        intro t ht
        simp only [Bool.and_eq_true,decide_eq_true_eq]
        constructor
        · rintro ⟨heq,_⟩
          have hp := congrArg T.position heq
          simpa only [T.position_cycle] using hp
        · intro heq
          subst t
          rw [T.cycle_position]
          exact ⟨rfl,hm⟩)
    simpa only [T,Function.comp_apply,List.mem_finRange,ite_true] using hc
  · rw [ite_eq_right hm]
    apply List.countP_eq_zero.mpr
    intro t ht
    simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq]
    rintro ⟨heq,hmark⟩
    rw [heq] at hmark
    exact hm hmark

/-- Decode actual bounded representative codes into literal configurations. -/
def addressOf {K : Nat} (r : Nat) (q : Vertex (K+1)) : Address K :=
  fun i => q.val.testBit (sparsePosition r i.val)
def epsilonOf {K : Nat} (r : Nat) (q : Vertex (K+1)) : Bool := q.val.testBit r

theorem code_of {K : Nat} (r : Nat) (hr : r<K+1) (q : Vertex (K+1)) :
    code r hr (epsilonOf r q) (addressOf r q)=q := by
  symm
  exact (eq_code_iff r hr _ _ q).mpr ⟨fun _ => rfl,rfl⟩

theorem address_of_code {K : Nat} (r : Nat) (hr : r<K+1) (b : Bool) (a : Address K) :
    addressOf r (code r hr b a)=a := funext (code_source r hr b a)
theorem epsilon_of_code {K : Nat} (r : Nat) (hr : r<K+1) (b : Bool) (a : Address K) :
    epsilonOf r (code r hr b a)=b := code_reserved r hr b a

/-- All configurations for one offset, each literal numeric code exactly once. -/
noncomputable def offsetList {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool) (u : Nat) :=
  (List.finRange (2^(k+h+1))).flatMap fun q =>
    markedVertices he C k h r hr S ho direction (epsilonOf r q) (addressOf r q) u

/-- Unconditional exact one-fold physical cover at each u, from the actual
owner theorem and list uniqueness, rather than an assumed multicover. -/
theorem offset_count {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1)
    (room : 2^(k+h+1)∣lengthPower (2^e) k) (direction : Bool→Address (k+h)→Bool)
    (depends : ∀ b a a', AgreeBelow r a a'→direction b a=direction b a')
    (u : Nat) (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (offsetList he C k h r hr S ho direction u).countP (fun w => decide (w=v))=1 := by
  classical
  obtain ⟨b,a,hm,hu⟩ := unique_mark_configuration he C k h r hr S ho room direction depends u v
  let owner := code r hr b a
  have hp (q : Vertex (k+h+1)) : Marked he C k h r hr S ho direction (epsilonOf r q) (addressOf r q) u v ↔ q=owner := by
    constructor
    · intro hmark
      obtain ⟨hb,ha⟩ := hu _ _ hmark
      rw [←code_of r hr q,hb,ha]
    · intro heq
      subst q
      simpa only [owner,epsilon_of_code,address_of_code] using hm
  rw [offsetList,List.countP_flatMap]
  have hf : (fun q : Vertex (k+h+1) => (fun l => l.countP (fun w => decide (w=v)))
      (markedVertices he C k h r hr S ho direction (epsilonOf r q) (addressOf r q) u))=
      (fun q => if q=owner then 1 else 0) := by
    funext q
    dsimp only
    rw [marked_list_count,hp]
    by_cases hq : q=owner <;> simp only [hq,ite_true,ite_false]
  change ((List.finRange (2^(k+h+1))).map _).sum=1
  simp only [Function.comp_def]
  rw [hf]
  have hs := indicator_sum (fun q => decide (q=owner)) (List.finRange (2^(k+h+1)))
  simp only [decide_eq_true_eq] at hs
  rw [hs]
  simpa only [List.mem_finRange,ite_true] using count_unique (List.finRange _) (List.nodup_finRange _)
    (fun q => decide (q=owner)) owner (by intro q hq; simp)

/-- Flatten actual physical mark lists for every u<b. -/
noncomputable def allMarks {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool) (b : Nat) :=
  (List.finRange b).flatMap fun u => offsetList he C k h r hr S ho direction u.val

theorem exact_multiplicity {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1)
    (room : 2^(k+h+1)∣lengthPower (2^e) k) (direction : Bool→Address (k+h)→Bool)
    (depends : ∀ d a a', AgreeBelow r a a'→direction d a=direction d a')
    (b : Nat) (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (allMarks he C k h r hr S ho direction b).countP (fun w => decide (w=v))=b := by
  classical
  rw [allMarks,List.countP_flatMap]
  have hf : (fun u : Fin b => (offsetList he C k h r hr S ho direction u.val).countP (fun w => decide (w=v)))=
      (fun _ => 1) := funext (fun u => offset_count he C k h r hr S ho room direction depends u.val v)
  change ((List.finRange b).map _).sum=b
  simp only [Function.comp_def]
  rw [hf]
  have hs := indicator_sum (fun _ : Fin b => true) (List.finRange b)
  simpa only [ite_true,List.countP_true,List.length_finRange] using hs

/-- Complete explicit phase positions of a residue in a P*T cycle. -/
def phasePosition {P T : Nat} (_hP : 0<P) (c : Fin P) (q : Fin T) : Fin (P*T) :=
  ⟨P*q.val+c.val,by
    have hq := Nat.mul_le_mul_left P (show q.val+1≤T by have := q.isLt; omega)
    rw [Nat.mul_add,Nat.mul_one] at hq
    have := c.isLt
    omega⟩

theorem phasePosition_injective {P T : Nat} (hP : 0<P) (c : Fin P) :
    Function.Injective (@phasePosition P T hP c) := by
  intro q q' he
  apply Fin.ext
  apply Nat.eq_of_mul_eq_mul_left hP
  have hh := congrArg Fin.val he
  change P*q.val+c.val=P*q'.val+c.val at hh
  omega

theorem phasePosition_mem {P T : Nat} (hP : 0<P) (c : Fin P) (n : Fin (P*T)) :
    n∈(List.finRange T).map (phasePosition hP c) ↔ n.val%P=c.val := by
  simp only [List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨q,rfl⟩
    simp only [phasePosition,Nat.mul_add_mod,Nat.mod_eq_of_lt c.isLt]
  · intro hn
    refine ⟨⟨n.val/P,Nat.div_lt_of_lt_mul n.isLt⟩,?_⟩
    apply Fin.ext
    change P*(n.val/P)+c.val=n.val
    rw [←hn]
    exact Nat.div_add_mod n.val P

/-- Exact explicit phase count; both lists enumerate actual positions once. -/
theorem residue_count {P T : Nat} (hP : 0<P) (c : Fin P) :
    (List.finRange (P*T)).countP (fun n => decide (n.val%P=c.val))=T := by
  classical
  let phases := (List.finRange T).map (phasePosition hP c)
  let retained := (List.finRange (P*T)).filter (fun n => decide (n.val%P=c.val))
  have hn : phases.Nodup := List.Pairwise.map _
    (fun q q' hne he => hne (phasePosition_injective hP c he)) (List.nodup_finRange T)
  have hr : retained.Nodup := List.Pairwise.filter _ (List.nodup_finRange (P*T))
  have hm (n : Fin (P*T)) : n∈phases ↔ n∈retained := by
    simp only [phases,retained,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
    exact phasePosition_mem hP c n
  have hle := hn.length_le_of_subset (fun n hn => (hm n).mp hn)
  have hge := hr.length_le_of_subset (fun n hn => (hm n).mpr hn)
  rw [List.countP_eq_length_filter]
  change retained.length=T
  have hh : phases.length=T := by simp [phases]
  omega

/-- Cyclic arithmetic membership is exactly a literal shifted phase residue. -/
theorem shift_phase_iff {P : Nat} (hP : 0<P) (delta n : Nat) (c : Fin P) :
    shiftedResidue P delta n=c.val ↔ n%P=(c.val+delta%P)%P := by
  let a : Fin P := ⟨n%P,Nat.mod_lt _ hP⟩
  let d : Fin P := ⟨delta%P,Nat.mod_lt _ hP⟩
  have hs : shiftedResidue P delta n=(SquareLift.backward hP a d).val := by
    simp only [shiftedResidue,SquareLift.backward,a,d,Nat.add_mod,Nat.mod_mod,Nat.add_comm]
  rw [hs]
  have hf := SquareLift.forward_inverse hP d a
  constructor
  · intro he
    have hc : SquareLift.backward hP a d=c := Fin.ext he
    rw [hc] at hf
    have hh := congrArg Fin.val hf
    simpa only [SquareLift.forward,a,d,Nat.add_comm] using hh.symm
  · intro he
    have hc : a=SquareLift.forward hP d c := Fin.ext (by
      simpa only [a,d,SquareLift.forward,Nat.add_comm] using he)
    have hb : SquareLift.backward hP a d=c :=
      SquareLift.forward_injective hP d (hf.trans hc)
    exact congrArg Fin.val hb

theorem shifted_phase_count {P T : Nat} (hP : 0<P) (delta : Nat) (c : Fin P) :
    (List.finRange (P*T)).countP (fun n => decide (shiftedResidue P delta n.val=c.val))=T := by
  have hc : (List.finRange (P*T)).countP (fun n => decide (shiftedResidue P delta n.val=c.val))=
      (List.finRange (P*T)).countP (fun n => decide (n.val%P=(c.val+delta%P)%P)) := by
    apply List.countP_congr
    intro n hn
    simp only [decide_eq_true_eq]
    exact shift_phase_iff hP delta n.val c
  exact hc.trans (residue_count hP ⟨(c.val+delta%P)%P,Nat.mod_lt _ hP⟩)

theorem full_phase_count {N P : Nat} (hP : 0<P) (hd : P∣N) (delta : Nat) (c : Fin P) :
    (List.finRange N).countP (fun n => decide (shiftedResidue P delta n.val=c.val))=N/P := by
  have he : N=P*(N/P) := (Nat.mul_div_cancel' hd).symm
  conv => lhs; rw [he]
  exact shifted_phase_count hP delta c

/-- Each actual configuration/u contains exactly full-cycle-length/P physical
marks. This is an explicit uniform phase count, not a balance assumption. -/
theorem representative_length {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1)
    (room : 2^(k+h+1)∣lengthPower (2^e) k) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (u : Nat) :
    (markedVertices he C k h r hr S ho direction epsilon address u).length=
      lengthPower ((2^(e*2^k))*(2^(e*2^k))) h / 2^(k+h+1) := by
  classical
  have hd : 2^(k+h+1)∣lengthPower ((2^(e*2^k))*(2^(e*2^k))) h := by
    have hp : 2^(k+h+1)∣2^(e*2^k) := by simpa only [lengthPower_pow] using room
    exact lengthPower_divisible (Nat.dvd_trans hp (Nat.dvd_mul_right _ _)) h
  rw [markedVertices,List.length_map,←List.countP_eq_length_filter]
  have hc : (List.finRange (lengthPower ((2^(e*2^k))*(2^(e*2^k))) h)).countP
      (fun t => decide (Marked he C k h r hr S ho direction epsilon address u
        ((clock he C k h S ho epsilon address).cycle t)))=
      (List.finRange (lengthPower ((2^(e*2^k))*(2^(e*2^k))) h)).countP
        (fun t => decide (shiftedResidue (2^(k+h+1))
          (signedOffset (2^(k+h+1)) (2^r) u (direction epsilon address)) t.val=
          (code r hr epsilon address).val)) := by
    apply List.countP_congr
    intro t ht
    simp only [decide_eq_true_eq,Marked,shiftedValue,(clock he C k h S ho epsilon address).position_cycle]
  exact hc.trans (full_phase_count (Nat.two_pow_pos _) hd _ (code r hr epsilon address))

private theorem constant_sum {X : Type} (l : List X) (n : Nat) :
    (l.map (fun _ => n)).sum=l.length*n := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.succ_mul,Nat.add_comm]

/-- The concrete representative word for one source/profile configuration. -/
noncomputable def configurationList {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (b : Nat) :=
  (List.finRange b).flatMap fun u => markedVertices he C k h r hr S ho direction epsilon address u.val

theorem configuration_length {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1)
    (room : 2^(k+h+1)∣lengthPower (2^e) k) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (b : Nat) :
    (configurationList he C k h r hr S ho direction epsilon address b).length=
      b*(lengthPower ((2^(e*2^k))*(2^(e*2^k))) h / 2^(k+h+1)) := by
  rw [configurationList,List.length_flatMap]
  have hf : (fun u : Fin b => (markedVertices he C k h r hr S ho direction epsilon address u.val).length)=
      (fun _ => lengthPower ((2^(e*2^k))*(2^(e*2^k))) h / 2^(k+h+1)) := by
    funext u
    exact representative_length he C k h r hr S ho room direction epsilon address u.val
  rw [hf,constant_sum,List.length_finRange]

private theorem sum_add {X : Type} (l : List X) (f g : X→Nat) :
    (l.map (fun x => f x+g x)).sum=(l.map f).sum+(l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons,List.sum_cons,ih]; omega

private theorem sum_swap {X Y : Type} (xs : List X) (ys : List Y) (f : X→Y→Nat) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum=
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil,constant_sum,Nat.mul_zero]
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [sum_add,ih]

/-- Configuration-indexed representative words have exactly the b-fold
incidence count required by downstream physical chord/mark interfaces. -/
theorem configuration_multiplicity {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1)
    (room : 2^(k+h+1)∣lengthPower (2^e) k) (direction : Bool→Address (k+h)→Bool)
    (depends : ∀ d a a', AgreeBelow r a a'→direction d a=direction d a')
    (b : Nat) (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ((List.finRange (2^(k+h+1))).map (fun q =>
      (configurationList he C k h r hr S ho direction (epsilonOf r q) (addressOf r q) b).countP
        (fun w => decide (w=v)))).sum=b := by
  classical
  simp only [configurationList,List.countP_flatMap,Function.comp_def]
  rw [sum_swap]
  have hf : (fun u : Fin b => ((List.finRange (2^(k+h+1))).map (fun q =>
      (markedVertices he C k h r hr S ho direction (epsilonOf r q) (addressOf r q) u.val).countP
        (fun w => decide (w=v)))).sum)=(fun _ => 1) := by
    funext u
    have hh := offset_count he C k h r hr S ho room direction depends u.val v
    simpa only [offsetList,List.countP_flatMap,Function.comp_def] using hh
  rw [hf,constant_sum,List.length_finRange,Nat.mul_one]

#print axioms configuration_multiplicity
#print axioms configuration_length
#print axioms representative_length
#print axioms shifted_phase_count
#print axioms exact_multiplicity
end ErdePaths.DenseSourceCounts
