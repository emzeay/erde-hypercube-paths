import ErdePaths.MersenneLargeUnmarks
import ErdePaths.DenseSourceCounts

namespace ErdePaths.MersenneComplement
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts DenseSourceMarks Profile
attribute [local instance] Classical.propDecidable

noncomputable def rawValue {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (delta : Nat) (a : Address (k+h)) : Nat :=
  shiftedResidue (2^(k+h+3)) delta ((clock he C k h S ho epsilon a).position v).val

/-- Numeric residue eligibility of an actual interior group. The later AAC
incidence equivalence remains separate from this actual-clock definition. -/
def Eligible {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (a : Address (k+h)) : Prop :=
  ((clock he C k h S ho epsilon a).position v).val.testBit 0=a ⟨0,by omega⟩

/-- All actual source/profile configurations share raw parity at the same
physical vertex, independently of every source choice and profile twin. -/
theorem parity_common {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (b b' : Bool) (a a' : Address (k+h))
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ((clock he C k h S ho b a).position v).val.testBit 0=
      ((clock he C k h S ho b' a').position v).val.testBit 0 := by
  apply MersenneDecode.bit_congr (n:=0)
  exact lower_prefix_common he C k h 0 (by omega) (by
    change 2^1∣2^e; exact Nat.pow_dvd_pow 2 (by omega)) S S ho ho b b' a a' (fun _ hi => by omega) v

/-- Literal oriented removal code, including profile bit and holes. -/
def RemovedAt {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (a : Address (k+h)) (j : Fin 4) : Prop :=
  rawValue he C k h S ho epsilon v (MersenneOffsets.delta (2^(k+h+1)) epsilon j) a=
    (MersenneCode.code (by omega) exceptional epsilon a).val

def Removed {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (a : Address (k+h)) : Prop :=
  ∃j : Fin 4, RemovedAt he C k h hk S ho exceptional epsilon v a j

/-- Actual literal unmarks are eligible: even shifts preserve actual clock
parity and every complete raw code has source a0 at numeric bit0. -/
theorem removed_eligible {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hK : 3≤k+h) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (a : Address (k+h))
    (hm : Removed he C k h hk S ho exceptional epsilon v a) :
    Eligible he C k h hk S ho epsilon v a := by
  obtain ⟨j,hj⟩ := hm
  have hp : 16≤2^(k+h+1) := Nat.pow_le_pow_right (show 1≤2 by decide) (show 4≤k+h+1 by omega)
  have hd := MersenneOffsets.delta_even hp epsilon j
  have hs := SourceParity.even_shift_bit (Nat.two_pow_pos (k+h+3))
    (show 2∣2^(k+h+3) by change 2^1∣2^(k+h+3); exact Nat.pow_dvd_pow 2 (by omega))
    (MersenneOffsets.delta (2^(k+h+1)) epsilon j)
    ((clock he C k h S ho epsilon a).position v).val hd
  have hc := congrFun (MersenneCode.code_bits (by omega : 2≤k+h) exceptional epsilon a) ⟨0,by omega⟩
  simp only [binaryTuple,MersenneCode.codeBits,↓reduceIte] at hc
  have hb := congrArg (fun n => n.testBit 0) hj
  exact hs.symm.trans (hb.trans hc)

/-- Exact number of actual parity-eligible configuration incidences. The
index is the dense bijective code, not the exceptional noninjective rawcode. -/
theorem eligible_count {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q)))=2^(k+h) := by
  let ref : Address (k+h) := fun _ => false
  let p := ((clock he C k h S ho false ref).position v).val.testBit 0
  have hc : (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q)))=
      (List.finRange (2^(k+h+1))).countP (fun q => decide (q.val%2=p.toNat)) := by
    apply List.countP_congr
    intro q hq
    simp only [decide_eq_true_eq]
    unfold Eligible
    rw [parity_common he C k h S ho (epsilonOf 1 q) false (addressOf 1 q) ref v]
    change p=q.val.testBit (sparsePosition 1 0) ↔ _
    simp only [sparsePosition]
    have hm : q.val%2<2 := Nat.mod_lt _ (by decide)
    cases p <;> simp <;> omega
  rw [hc]
  have hP : 2^(k+h+1)=2*2^(k+h) := by rw [Nat.pow_succ,Nat.mul_comm]
  conv => lhs; rw [hP]
  exact residue_count (by decide : 0<2) ⟨p.toNat,by cases p <;> decide⟩

private theorem count_unique {X : Type} [DecidableEq X] (l : List X) (hn : l.Nodup)
    (p : X→Bool) (owner : X) (hp : ∀ x∈l, p x=true ↔ x=owner) :
    l.countP p=if owner∈l then 1 else 0 := by
  classical
  have hc : l.countP p=l.count owner := by
    apply List.countP_congr
    intro x hx
    simpa only [beq_iff_eq] using hp x hx
  exact hc.trans hn.count

private theorem count_remove {X : Type} (l : List X) (E R : X→Prop)
    (sub : ∀x, R x→E x) :
    l.countP (fun x => decide (E x ∧ ¬R x))+l.countP (fun x => decide (R x))=
      l.countP (fun x => decide (E x)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases he : E x <;> by_cases hr : R x <;> simp_all <;> omega

private theorem retained_count {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hK : 3≤k+h) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (owner : ∃b a, Removed he C k h hk S ho exceptional b v a ∧
      ∀b' a', Removed he C k h hk S ho exceptional b' v a'→b'=b ∧ a'=a) :
    (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q)))=2^(k+h)-1 := by
  classical
  obtain ⟨b,a,hm,hu⟩ := owner
  let q0 := DenseSourceMarks.code 1 (show 1<k+h+1 by omega) b a
  have hp (q : Vertex (k+h+1)) : Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q) ↔ q=q0 := by
    constructor
    · intro hq
      obtain ⟨hb,ha⟩ := hu _ _ hq
      rw [←code_of 1 (by omega) q,hb,ha]
    · intro hq
      subst q
      simpa only [q0,epsilon_of_code,address_of_code] using hm
  have hr : (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q)))=1 := by
    have hc := count_unique (List.finRange _) (List.nodup_finRange _)
      (fun q => decide (Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q))) q0
      (by intro q hq; simp only [decide_eq_true_eq]; exact hp q)
    simpa only [List.mem_finRange,ite_true] using hc
  have hh := count_remove (List.finRange (2^(k+h+1)))
    (fun q => Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q))
    (fun q => Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q))
    (fun q hm => removed_eligible he C k h hk hK S ho exceptional (epsilonOf 1 q) v (addressOf 1 q) hm)
  rw [hr,eligible_count] at hh
  have hs := congrArg (fun n : Nat => n-1) hh
  simp only [Nat.add_sub_cancel] at hs
  apply Eq.trans ?_ hs
  apply List.countP_congr
  intro q hq
  simp only [decide_eq_true_eq]

/-- Actual exceptional unmark construction supplies the sole removal. -/
theorem small_retained_count {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (hK : 1≤t+h) (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool)
    (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    (List.finRange (2^(t+2+h+1))).countP (fun q => decide
      (Eligible (by omega) C (t+2) h (by omega) S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed (by omega) C (t+2) h (by omega) S ho true (epsilonOf 1 q) v (addressOf 1 q)))=2^(t+2+h)-1 := by
  apply retained_count (by omega) C (t+2) h (by omega) (by omega) S ho true v
  obtain ⟨b,j,a,hm,hu⟩ := MersenneCode.unique_code_owner C t h hK S ho v
  refine ⟨b,a,⟨j,hm⟩,?_⟩
  intro b' a' hm'
  obtain ⟨j',hj'⟩ := hm'
  obtain ⟨hb,_,ha⟩ := hu b' j' a' hj'
  exact ⟨hb,ha⟩

/-- Actual larger-base raw unmark construction supplies the sole removal. -/
theorem large_retained_count {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hK : 3≤k+h)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Eligible (by omega) C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed (by omega) C k h hk S ho false (epsilonOf 1 q) v (addressOf 1 q)))=2^(k+h)-1 := by
  apply retained_count (by omega) C k h hk hK S ho false v
  obtain ⟨b,j,a,hm,hu⟩ := MersenneLargeUnmarks.unique_code_owner he C k h hk hK S ho v
  refine ⟨b,a,⟨j,hm⟩,?_⟩
  intro b' a' hm'
  obtain ⟨j',hj'⟩ := hm'
  obtain ⟨hb,_,ha⟩ := hu b' j' a' hj'
  exact ⟨hb,ha⟩

noncomputable def physicalWord {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional epsilon : Bool) (a : Address (k+h)) :=
  ((List.finRange (lengthPower ((2^(e*2^k))*(2^(e*2^k))) h)).filter (fun t => decide
    (Eligible he C k h hk S ho epsilon ((clock he C k h S ho epsilon a).cycle t) a ∧
      ¬Removed he C k h hk S ho exceptional epsilon ((clock he C k h S ho epsilon a).cycle t) a))).map
    (clock he C k h S ho epsilon a).cycle

private theorem physicalWord_count {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional epsilon : Bool) (a : Address (k+h))
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (physicalWord he C k h hk S ho exceptional epsilon a).countP (fun w => decide (w=v))=
      if Eligible he C k h hk S ho epsilon v a ∧ ¬Removed he C k h hk S ho exceptional epsilon v a
      then 1 else 0 := by
  classical
  rw [physicalWord,List.countP_map,List.countP_filter]
  let T := clock he C k h S ho epsilon a
  let P := fun v => Eligible he C k h hk S ho epsilon v a ∧ ¬Removed he C k h hk S ho exceptional epsilon v a
  by_cases hm : P v
  · rw [ite_eq_left hm]
    have hc := count_unique (List.finRange _) (List.nodup_finRange _)
      (fun t => decide (T.cycle t=v) && decide (P (T.cycle t))) (T.position v) (by
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
    simpa only [T,P,Function.comp_apply,List.mem_finRange,ite_true] using hc
  · rw [ite_eq_right hm]
    apply List.countP_eq_zero.mpr
    intro t ht
    simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq]
    rintro ⟨heq,hmark⟩
    rw [heq] at hmark
    exact hm hmark

noncomputable def physicalMarks {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional : Bool) :=
  (List.finRange (2^(k+h+1))).flatMap fun q => physicalWord he C k h hk S ho exceptional
    (epsilonOf 1 q) (addressOf 1 q)

private theorem indicator_sum {X : Type} (p : X→Bool) (l : List X) :
    (l.map (fun x => if p x then 1 else 0)).sum=l.countP p := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons,List.sum_cons,List.countP_cons,ih]; omega

private theorem physical_count_eq {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (physicalMarks he C k h hk S ho exceptional).countP (fun w => decide (w=v))=
    (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q))) := by
  rw [physicalMarks,List.countP_flatMap]
  simp only [Function.comp_def]
  have hf : (fun q : Vertex (k+h+1) => (physicalWord he C k h hk S ho exceptional
      (epsilonOf 1 q) (addressOf 1 q)).countP (fun w => decide (w=v)))=
    (fun q => if Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q) then 1 else 0) := by
    funext q
    exact physicalWord_count he C k h hk S ho exceptional (epsilonOf 1 q) (addressOf 1 q) v
  rw [hf]
  have hs := indicator_sum (fun q : Vertex (k+h+1) => decide
      (Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q))) (List.finRange (2^(k+h+1)))
  simpa only [decide_eq_true_eq] using hs

/-- Genuine literal physical lists have L-1 incidence multiplicity at every
vertex in the exceptional small-base hierarchy. -/
theorem small_physical_multicover {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (hK : 1≤t+h) (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool)
    (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    (physicalMarks (by omega) C (t+2) h (by omega) S ho true).countP (fun w => decide (w=v))=2^(t+2+h)-1 :=
  (physical_count_eq (by omega) C (t+2) h (by omega) S ho true v).trans
    (small_retained_count C t h hK S ho v)

/-- The same actual L-1 physical multicover holds at every larger base. -/
theorem large_physical_multicover {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hK : 3≤k+h)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (physicalMarks (by omega) C k h hk S ho false).countP (fun w => decide (w=v))=2^(k+h)-1 :=
  (physical_count_eq (by omega) C k h hk S ho false v).trans
    (large_retained_count he C k h hk hK S ho v)

#print axioms small_physical_multicover
#print axioms large_physical_multicover
#print axioms small_retained_count
#print axioms large_retained_count
#print axioms eligible_count
#print axioms removed_eligible
end ErdePaths.MersenneComplement
