import ErdePaths.SourceStability
import ErdePaths.SourceParity

namespace ErdePaths.DenseSourceMarks
open SourceClock SourceProfile SourceStability HierarchicalDecode SquareLift

/-- Every bit is literal: the reserved slot holds epsilon and the remaining
slots hold the source address, with no unconstrained holes. -/
def codeBits {K : Nat} (r : Nat) (hr : r<K+1) (epsilon : Bool) (address : Address K) : Fin (K+1)→Bool :=
  fun i => if he : i.val=r then epsilon else
    if hi : i.val<r then address ⟨i.val,by have := i.isLt; omega⟩
    else address ⟨i.val-1,by have := i.isLt; omega⟩

noncomputable def code {K : Nat} (r : Nat) (hr : r<K+1) (epsilon : Bool) (address : Address K) :
    Vertex (K+1) := Classical.choose (binaryTuple_surjective (codeBits r hr epsilon address))

theorem code_bits {K : Nat} (r : Nat) (hr : r<K+1) (epsilon : Bool) (address : Address K) :
    binaryTuple (code r hr epsilon address)=codeBits r hr epsilon address :=
  Classical.choose_spec (binaryTuple_surjective (codeBits r hr epsilon address))

theorem code_reserved {K : Nat} (r : Nat) (hr : r<K+1) (epsilon : Bool) (address : Address K) :
    (code r hr epsilon address).val.testBit r=epsilon := by
  have h := congrFun (code_bits r hr epsilon address) ⟨r,hr⟩
  simpa only [binaryTuple,codeBits,dite_true] using h

theorem code_source {K : Nat} (r : Nat) (hr : r<K+1) (epsilon : Bool) (address : Address K) (i : Fin K) :
    (code r hr epsilon address).val.testBit (sparsePosition r i.val)=address i := by
  have h := congrFun (code_bits r hr epsilon address) ⟨sparsePosition r i.val,sparsePosition_lt r K i⟩
  unfold sparsePosition at h ⊢
  by_cases hi : i.val<r
  · simpa only [binaryTuple,codeBits,ite_eq_left hi,dite_eq_right (show i.val≠r by omega),dite_eq_left hi] using h
  · simp only [binaryTuple,codeBits,ite_eq_right hi,dite_eq_right (show i.val+1≠r by omega),
      dite_eq_right (show ¬i.val+1<r by omega)] at h
    simpa only [ite_eq_right hi,Nat.add_sub_cancel] using h

/-- Numeric representative equality is exactly the complete joint bit code. -/
theorem eq_code_iff {K : Nat} (r : Nat) (hr : r<K+1) (epsilon : Bool) (address : Address K)
    (x : Vertex (K+1)) : x=code r hr epsilon address ↔
      (∀ i : Fin K, x.val.testBit (sparsePosition r i.val)=address i) ∧ x.val.testBit r=epsilon := by
  constructor
  · rintro rfl
    exact ⟨code_source r hr epsilon address,code_reserved r hr epsilon address⟩
  · rintro ⟨hs,he⟩
    apply binaryTuple_injective
    funext i
    rw [code_bits]
    unfold binaryTuple codeBits
    by_cases hir : i.val=r
    · simpa only [dite_eq_left hir,hir,dite_true] using he
    · simp only [dite_eq_right hir]
      by_cases hil : i.val<r
      · simp only [dite_eq_left hil]
        have hh := hs ⟨i.val,by have := i.isLt; omega⟩
        simpa only [sparsePosition,ite_eq_left hil] using hh
      · simp only [dite_eq_right hil]
        have hh := hs ⟨i.val-1,by have := i.isLt; omega⟩
        have hn : ¬i.val-1<r := by omega
        simpa only [sparsePosition,ite_eq_right hn,show i.val-1+1=i.val by omega] using hh

/-- Explicit physical residue class: all complete phase-P translates along
this genuine source cycle, shifted by its actual oriented A*u offset. -/
def Marked {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (u : Nat)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) : Prop :=
  shiftedValue he C k h S ho epsilon v
    (signedOffset (2^(k+h+1)) (2^r) u (direction epsilon address)) address=
      (code r hr epsilon address).val

/-- Membership in the literal complete residue class is equivalent to the
already checked actual source/profile owner equations. -/
theorem marked_iff {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (u : Nat)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    Marked he C k h r hr S ho direction epsilon address u v ↔
      address=shiftedBits he C k h r S ho epsilon v
        (signedOffset (2^(k+h+1)) (2^r) u (direction epsilon address)) address ∧
      epsilon=(shiftedValue he C k h S ho epsilon v
        (signedOffset (2^(k+h+1)) (2^r) u (direction epsilon address)) address).testBit r := by
  let x : Vertex (k+h+1) := ⟨shiftedValue he C k h S ho epsilon v
    (signedOffset (2^(k+h+1)) (2^r) u (direction epsilon address)) address,
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  have hc := eq_code_iff r hr epsilon address x
  change x.val=(code r hr epsilon address).val ↔ _
  rw [←Fin.ext_iff,hc]
  constructor
  · rintro ⟨hs,hb⟩
    exact ⟨funext (fun i => (hs i).symm),hb.symm⟩
  · rintro ⟨hs,hb⟩
    exact ⟨fun i => (congrFun hs i).symm,hb.symm⟩

/-- Every physical vertex has exactly one actual source/profile configuration
for each specified u. This derives ownership rather than assuming it. -/
theorem unique_mark_configuration {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1)
    (room : 2^(k+h+1)∣lengthPower (2^e) k)
    (direction : Bool→Address (k+h)→Bool)
    (depends : ∀ b a a', AgreeBelow r a a' → direction b a=direction b a')
    (u : Nat) (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ∃ epsilon address, Marked he C k h r hr S ho direction epsilon address u v ∧
      ∀ b a, Marked he C k h r hr S ho direction b a u v → b=epsilon ∧ a=address := by
  obtain ⟨b,a,ha,hb,hu⟩ := unique_oriented_owner he C k h r hr S ho room v u direction depends
  refine ⟨b,a,(marked_iff he C k h r hr S ho direction b a u v).mpr ⟨ha,hb⟩,?_⟩
  intro b' a' hm
  obtain ⟨ha',hb'⟩ := (marked_iff he C k h r hr S ho direction b' a' u v).mp hm
  exact hu b' a' ha' hb'

theorem shift_cancel {P : Nat} (hP : 0<P) (d d' x : Nat)
    (he : shiftedResidue P d x=shiftedResidue P d' x) : d%P=d'%P := by
  have hh : backward hP (⟨x%P,Nat.mod_lt _ hP⟩ : Fin P) ⟨d%P,Nat.mod_lt _ hP⟩=
      backward hP ⟨x%P,Nat.mod_lt _ hP⟩ ⟨d'%P,Nat.mod_lt _ hP⟩ := by
    apply Fin.ext
    simpa only [backward,shiftedResidue,Nat.add_mod,Nat.mod_mod,Nat.add_comm] using he
  exact congrArg Fin.val (backward_injective hP _ hh)

theorem offset_injective {P A L : Nat} (hP : 0<P) (hA : 0<A) (hPL : P=A*L)
    (u u' : Nat) (hu : u<L) (hu' : u'<L) (b : Bool)
    (he : signedOffset P A u b%P=signedOffset P A u' b%P) : u=u' := by
  have hau : A*u<P := by rw [hPL]; exact Nat.mul_lt_mul_of_pos_left hu hA
  have hau' : A*u'<P := by rw [hPL]; exact Nat.mul_lt_mul_of_pos_left hu' hA
  cases b
  · simp only [signedOffset,Bool.false_eq_true,ite_false,Nat.mod_eq_of_lt hau,
      Nat.mod_eq_of_lt hau'] at he
    exact Nat.eq_of_mul_eq_mul_left hA he
  · have hh : shiftedResidue P (A*u) 0=shiftedResidue P (A*u') 0 := by
      simpa only [signedOffset,ite_true,shiftedResidue,Nat.mod_mod] using he
    have hc := shift_cancel hP (A*u) (A*u') 0 hh
    rw [Nat.mod_eq_of_lt hau,Nat.mod_eq_of_lt hau'] at hc
    exact Nat.eq_of_mul_eq_mul_left hA hc

/-- Different bounded u cannot mark one physical vertex in a fixed actual
configuration. Full phase translates therefore cannot introduce repetitions. -/
theorem marked_offset_unique {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (u u' : Nat)
    (hu : u<2^(k+h+1-r)) (hu' : u'<2^(k+h+1-r))
    (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (hm : Marked he C k h r hr S ho direction epsilon address u v)
    (hm' : Marked he C k h r hr S ho direction epsilon address u' v) : u=u' := by
  apply offset_injective (Nat.two_pow_pos _) (Nat.two_pow_pos r)
    (show 2^(k+h+1)=2^r*2^(k+h+1-r) by rw [←Nat.pow_add]; congr 1; omega)
    u u' hu hu' (direction epsilon address)
  exact shift_cancel (Nat.two_pow_pos _) _ _ _ (hm.trans hm'.symm)

/-- Canonical finite actual marked vertices: visit every literal cyclic
position once and retain exactly the complete oriented residue class. -/
noncomputable def markedVertices {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (u : Nat) :
    List (VertexPower (VertexPower V k×VertexPower V k) h) := by
  classical
  exact ((List.finRange (lengthPower ((2^(e*2^k))*(2^(e*2^k))) h)).filter
    (fun t => decide (Marked he C k h r hr S ho direction epsilon address u
      ((clock he C k h S ho epsilon address).cycle t)))).map
    (clock he C k h S ho epsilon address).cycle

/-- Canonical lists enumerate exactly the literal physical residue classes. -/
theorem mem_markedVertices {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (u : Nat)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    v∈markedVertices he C k h r hr S ho direction epsilon address u ↔
      Marked he C k h r hr S ho direction epsilon address u v := by
  classical
  simp only [markedVertices,List.mem_map,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  constructor
  · rintro ⟨t,hm,rfl⟩
    exact hm
  · intro hm
    refine ⟨(clock he C k h S ho epsilon address).position v,?_,?_⟩
    · simpa only [(clock he C k h S ho epsilon address).cycle_position] using hm
    · exact (clock he C k h S ho epsilon address).cycle_position v

#print axioms mem_markedVertices
#print axioms marked_offset_unique
#print axioms marked_iff
#print axioms unique_mark_configuration
end ErdePaths.DenseSourceMarks
