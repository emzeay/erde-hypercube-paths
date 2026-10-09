import ErdePaths.Profile
import ErdePaths.AnchoredEmbedding

namespace ErdePaths.AACTransition
open SquareLift SourceClock Profile

/-- Coarse grid points; vertical/base edges will be subdivided A times. -/
abbrev Grid (K B : Nat) := Fin K × Fin B
abbrev Fine (K A B : Nat) := Fin (K*A) × Fin B
abbrev FineEdge (K A B : Nat) := (Fin (K*A) × Fin B) ⊕ (Fin K × Fin B)

def gridPoint {K A B : Nat} (hA : 0<A) (v : Grid K B) : Fine K A B :=
  (AnchoredEmbedding.positionEncode v.1 ⟨0,hA⟩,v.2)

/-- All fine base-cycle edges, but second-axis edges only at actual grids. -/
def decode {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) :
    FineEdge K A B → Fine K A B × Fine K A B
  | .inl (x,j) => ((x,j),(successor (Nat.mul_pos hK hA) x,j))
  | .inr (i,j) => (gridPoint hA (i,j),gridPoint hA (i,successor hB j))

def Adjacent {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (u v : Fine K A B) : Prop := ∃ e, SameEdge (decode hK hA hB e) (u,v)

/-- Incoming ports point back along the edge just traversed. -/
inductive Port where
  | up | right | down | left
  deriving DecidableEq, Repr
abbrev State (K B : Nat) := Fin K × Fin B × Port

def pair (t : Bool) : Port → Port
  | .up => if t then .left else .right
  | .right => if t then .down else .up
  | .down => if t then .right else .left
  | .left => if t then .up else .down

theorem pair_involutive (t : Bool) (p : Port) : pair t (pair t p)=p := by
  cases t <;> cases p <;> rfl

def atPair {K B : Nat} (turns : Grid K B → Bool) (s : State K B) : State K B :=
  (s.1,s.2.1,pair (turns (s.1,s.2.1)) s.2.2)

theorem atPair_involutive {K B : Nat} (turns : Grid K B → Bool) (s : State K B) :
    atPair turns (atPair turns s)=s := by
  rcases s with ⟨i,j,p⟩
  simp only [atPair,pair_involutive]

/-- Cross the selected coarse edge, recording its opposite incoming port. -/
def cross {K B : Nat} (hK : 0<K) (hB : 0<B) (s : State K B) : State K B :=
  match s.2.2 with
  | .up => (successor hK s.1,s.2.1,.down)
  | .right => (s.1,successor hB s.2.1,.left)
  | .down => (predecessor hK s.1,s.2.1,.up)
  | .left => (s.1,predecessor hB s.2.1,.right)

theorem cross_involutive {K B : Nat} (hK : 0<K) (hB : 0<B) (s : State K B) :
    cross hK hB (cross hK hB s)=s := by
  rcases s with ⟨i,j,p⟩
  cases p <;> simp [cross,successor_predecessor,predecessor_successor]

def transition {K B : Nat} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B → Bool) (s : State K B) := cross hK hB (atPair turns s)
def inverseTransition {K B : Nat} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B → Bool) (s : State K B) := atPair turns (cross hK hB s)

theorem inverse_transition {K B : Nat} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B → Bool) (s : State K B) :
    inverseTransition hK hB turns (transition hK hB turns s)=s := by
  simp only [transition,inverseTransition,cross_involutive,atPair_involutive]

theorem transition_inverse {K B : Nat} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B → Bool) (s : State K B) :
    transition hK hB turns (inverseTransition hK hB turns s)=s := by
  simp only [transition,inverseTransition,atPair_involutive,cross_involutive]

theorem transition_bijective {K B : Nat} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B → Bool) :
    Function.Injective (transition hK hB turns) ∧ Function.Surjective (transition hK hB turns) := by
  constructor
  · intro s v h
    have hh := congrArg (inverseTransition hK hB turns) h
    simpa only [inverse_transition] using hh
  · intro s; exact ⟨inverseTransition hK hB turns s,transition_inverse hK hB turns s⟩

def signedNext {B : Nat} (hB : 0<B) (b : Bool) (j : Fin B) : Fin B :=
  if b then successor hB j else predecessor hB j

def baselineMacro {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool) (v : Grid K B) : Grid K B :=
  (successor hK v.1,signedNext hB (t v.1) v.2)

/-- Two actual port transitions give one positively oriented baseline macro. -/
theorem baseline_two_steps {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool) (v : Grid K B) :
    transition hK hB (fun w => t w.1)
      (transition hK hB (fun w => t w.1) (v.1,v.2,Port.down)) =
        ((baselineMacro hK hB t v).1,(baselineMacro hK hB t v).2,Port.down) := by
  rcases v with ⟨i,j⟩
  cases h : t i <;> simp [transition,atPair,pair,cross,baselineMacro,signedNext,h]


/-- Signed horizontal drift, computed from actual prefix turn counts. -/
def drift {K B : Nat} (hB : 0<B) (t : Fin K → Bool) (n : Nat) : Fin B :=
  ⟨(prefixCount t n+(B-1)*prefixCount (colorSet t true) n)%B,Nat.mod_lt _ hB⟩

def BalancedTurns {K : Nat} (t : Fin K → Bool) : Prop :=
  cardinality t=cardinality (colorSet t true)

theorem drift_zero {K B : Nat} (hB : 0<B) (t : Fin K → Bool) :
    drift hB t 0=⟨0,hB⟩ := by
  apply Fin.ext
  simp [drift,prefixCount]

theorem drift_balanced_end {K B : Nat} (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) : drift hB t K=⟨0,hB⟩ := by
  unfold BalancedTurns cardinality at hb
  apply Fin.ext
  simp only [drift]
  rw [hb]
  have he : prefixCount (colorSet t true) K+(B-1)*prefixCount (colorSet t true) K=
      B*prefixCount (colorSet t true) K := by
    have hh := Nat.add_mul 1 (B-1) (prefixCount (colorSet t true) K)
    simp only [Nat.one_mul] at hh
    have hB' : 1+(B-1)=B := by omega
    rw [hB'] at hh
    exact hh.symm
  rw [he,Nat.mul_mod_right]

theorem drift_step {K B : Nat} (hB : 0<B) (t : Fin K → Bool) (n : Nat) (hn : n<K) :
    drift hB t (n+1)=signedNext hB (t ⟨n,hn⟩) (drift hB t n) := by
  apply Fin.ext
  simp only [drift,prefixCount,indicator,dite_eq_left hn,colorSet,Bool.xor_true]
  cases ht : t ⟨n,hn⟩
  · simp only [Bool.toNat_false,Bool.not_false,Bool.toNat_true,Nat.add_zero,signedNext,
      Bool.false_eq_true,↓reduceIte,predecessor]
    rw [Nat.mul_add,Nat.mul_one,Nat.add_mod_mod]
    congr 1
    omega
  · simp only [Bool.toNat_true,Bool.not_true,Bool.toNat_false,Nat.add_zero,signedNext,
      ↓reduceIte,successor]
    rw [Nat.mod_add_mod]
    congr 1
    omega

/-- Balanced drift also satisfies the cyclic seam, not only interior recurrence. -/
theorem drift_cyclic {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (i : Fin K) :
    drift hB t (successor hK i).val=signedNext hB (t i) (drift hB t i.val) := by
  have hs := drift_step hB t i.val i.isLt
  by_cases hi : i.val+1<K
  · have he : (successor hK i).val=i.val+1 := Nat.mod_eq_of_lt hi
    simpa only [he] using hs
  · have hi' : i.val+1=K := by have := i.isLt; omega
    have hz : (successor hK i).val=0 := by simp [successor,hi']
    rw [hi',drift_balanced_end hB t hb] at hs
    simpa only [hz,drift_zero] using hs

theorem signedNext_forward {B : Nat} (hB : 0<B) (b : Bool) (x y : Fin B) :
    signedNext hB b (forward hB x y)=forward hB (signedNext hB b x) y := by
  apply Fin.ext
  cases b
  · simp only [signedNext,Bool.false_eq_true,↓reduceIte,forward,predecessor,
      Nat.add_mod_mod,Nat.mod_add_mod]
    congr 1
    omega
  · simp only [signedNext,↓reduceIte,forward,successor,Nat.mod_add_mod]
    congr 1
    omega

/-- Every baseline loop has an actual physical grid enumeration. -/
def baselinePoint {K B : Nat} (hB : 0<B) (t : Fin K → Bool) (label : Fin B) (i : Fin K) : Grid K B :=
  (i,forward hB (drift hB t i.val) label)

theorem baselinePoint_next {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (label : Fin B) (i : Fin K) :
    baselineMacro hK hB t (baselinePoint hB t label i)=baselinePoint hB t label (successor hK i) := by
  apply Prod.ext
  · rfl
  change signedNext hB (t i) (forward hB (drift hB t i.val) label)=_
  rw [signedNext_forward,←drift_cyclic hK hB t hb i]
  rfl


def baselineLabel {K B : Nat} (hB : 0<B) (t : Fin K → Bool) (v : Grid K B) : Fin B :=
  backward hB v.2 (drift hB t v.1.val)

theorem baselinePoint_label {K B : Nat} (hB : 0<B) (t : Fin K → Bool) (v : Grid K B) :
    baselinePoint hB t (baselineLabel hB t v) v.1=v := by
  apply Prod.ext
  · rfl
  · exact forward_inverse hB (drift hB t v.1.val) v.2

theorem baselineLabel_point {K B : Nat} (hB : 0<B) (t : Fin K → Bool) (label : Fin B) (i : Fin K) :
    baselineLabel hB t (baselinePoint hB t label i)=label := by
  apply forward_injective hB (drift hB t i.val)
  exact forward_inverse hB (drift hB t i.val) (forward hB (drift hB t i.val) label)

theorem baselinePoint_injective {K B : Nat} (hB : 0<B) (t : Fin K → Bool) :
    Function.Injective (fun p : Fin B × Fin K => baselinePoint hB t p.1 p.2) := by
  intro p v h
  have hi : p.2=v.2 := congrArg Prod.fst h
  have hl := congrArg (baselineLabel hB t) h
  rw [baselineLabel_point,baselineLabel_point] at hl
  exact Prod.ext hl hi

/-- The proved drift invariant is an actual finite physical-grid function. -/
theorem baselineLabel_invariant {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (v : Grid K B) :
    baselineLabel hB t (baselineMacro hK hB t v)=baselineLabel hB t v := by
  rw [←baselinePoint_label hB t v,baselinePoint_next hK hB t hb]
  rw [baselineLabel_point,baselineLabel_point]

/-- A concrete 2K-step baseline circuit: G-arrival then H-arrival at each
column. This is a circuit of directed states, not a Hamilton vertex claim. -/
def baselineLoop {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (label : Fin B) (p : Fin K × Bool) : State K B :=
  let v := baselinePoint hB t label p.1
  if p.2 then transition hK hB (fun w => t w.1) (v.1,v.2,.down)
    else (v.1,v.2,.down)

def loopNext {K : Nat} (hK : 0<K) (p : Fin K × Bool) : Fin K × Bool :=
  if p.2 then (successor hK p.1,false) else (p.1,true)

theorem baselineLoop_next {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (label : Fin B) (p : Fin K × Bool) :
    transition hK hB (fun w => t w.1) (baselineLoop hK hB t label p)=
      baselineLoop hK hB t label (loopNext hK p) := by
  rcases p with ⟨i,b⟩
  cases b
  · rfl
  · simp only [baselineLoop,loopNext,↓reduceIte]
    rw [baseline_two_steps,baselinePoint_next hK hB t hb]
    simp only [Bool.false_eq_true,↓reduceIte]

private theorem first_states_injective {K B : Nat} (hB : 0<B) (t : Fin K → Bool)
    (label label' : Fin B) (i i' : Fin K)
    (h : ((baselinePoint hB t label i).1,(baselinePoint hB t label i).2,Port.down)=
      ((baselinePoint hB t label' i').1,(baselinePoint hB t label' i').2,Port.down)) :
    label=label' ∧ i=i' := by
  have hh : baselinePoint hB t label i=baselinePoint hB t label' i' :=
    Prod.ext (congrArg (fun s : State K B => s.1) h) (congrArg (fun s : State K B => s.2.1) h)
  have hp : (label,i)=(label',i') := baselinePoint_injective hB t hh
  exact ⟨congrArg Prod.fst hp,congrArg Prod.snd hp⟩

/-- Circuit labels and their 2K positions are distinct as directed states. -/
theorem baselineLoop_injective {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool) :
    Function.Injective (fun p : Fin B × Fin K × Bool => baselineLoop hK hB t p.1 p.2) := by
  intro p v h
  rcases p with ⟨label,i,b⟩
  rcases v with ⟨label',i',b'⟩
  cases b <;> cases b'
  · obtain ⟨hl,hi⟩ := first_states_injective hB t label label' i i' h
    subst label'; subst i'; rfl
  · have hp := congrArg (fun s : State K B => s.2.2) h
    change Port.down=(transition hK hB (fun w => t w.1)
      ((baselinePoint hB t label' i').1,(baselinePoint hB t label' i').2,Port.down)).2.2 at hp
    cases ht : t i' <;> simp [transition,atPair,pair,cross,baselinePoint,ht] at hp
  · have hp := congrArg (fun s : State K B => s.2.2) h
    change (transition hK hB (fun w => t w.1)
      ((baselinePoint hB t label i).1,(baselinePoint hB t label i).2,Port.down)).2.2=Port.down at hp
    cases ht : t i <;> simp [transition,atPair,pair,cross,baselinePoint,ht] at hp
  · have hh := congrArg (inverseTransition hK hB (fun w => t w.1)) h
    simp only [baselineLoop,↓reduceIte,inverse_transition] at hh
    obtain ⟨hl,hi⟩ := first_states_injective hB t label label' i i' hh
    subst label'; subst i'; rfl

/-- Reversing a circuit uses the complementary incoming port at each grid. -/
theorem reversal_relation {K B : Nat} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B → Bool) (s : State K B) :
    atPair turns (transition hK hB turns s)=
      inverseTransition hK hB turns (atPair turns s) := by
  simp only [transition,inverseTransition]


/-- Positive G-oriented baseline circuits use precisely these incoming ports. -/
def PositiveState {K B : Nat} (t : Fin K → Bool) (s : State K B) : Prop :=
  s.2.2=.down ∨ s.2.2=(if t s.1 then Port.left else Port.right)

theorem baselineLoop_positive {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (label : Fin B) (p : Fin K × Bool) :
    PositiveState t (baselineLoop hK hB t label p) := by
  rcases p with ⟨i,b⟩
  cases b
  · exact Or.inl rfl
  · cases ht : t i <;> simp [PositiveState,baselineLoop,transition,atPair,pair,cross,baselinePoint,ht]

theorem baselineLoop_covers_positive {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (s : State K B) (hs : PositiveState t s) :
    ∃ label p, baselineLoop hK hB t label p=s := by
  rcases hs with hs | hs
  · let v : Grid K B := (s.1,s.2.1)
    have hv := baselinePoint_label hB t v
    refine ⟨baselineLabel hB t v,(s.1,false),?_⟩
    change ((baselinePoint hB t (baselineLabel hB t v) s.1).1,
      (baselinePoint hB t (baselineLabel hB t v) s.1).2,Port.down)=s
    rw [hv]
    exact Prod.ext rfl (Prod.ext rfl hs.symm)
  · let u := inverseTransition hK hB (fun w => t w.1) s
    have hu : u.2.2=Port.down := by
      dsimp [u,inverseTransition,cross,atPair]
      rcases s with ⟨i,j,p⟩
      cases ht : t i <;> simp only [ht,↓reduceIte] at hs
      · subst p; simp [pair,ht]
      · subst p; simp [pair,ht]
    let v : Grid K B := (u.1,u.2.1)
    have hv := baselinePoint_label hB t v
    have hstate : ((baselinePoint hB t (baselineLabel hB t v) u.1).1,
      (baselinePoint hB t (baselineLabel hB t v) u.1).2,Port.down)=u := by
      rw [hv]
      exact Prod.ext rfl (Prod.ext rfl hu.symm)
    refine ⟨baselineLabel hB t v,(u.1,true),?_⟩
    change transition hK hB (fun w => t w.1)
      ((baselinePoint hB t (baselineLabel hB t v) u.1).1,
       (baselinePoint hB t (baselineLabel hB t v) u.1).2,Port.down)=s
    rw [hstate]
    exact transition_inverse hK hB (fun w => t w.1) s

/-- Every directed state is in a positive circuit or its reverse. -/
theorem positive_or_reverse {K B : Nat} (t : Fin K → Bool) (s : State K B) :
    PositiveState t s ∨ PositiveState t (atPair (fun w => t w.1) s) := by
  rcases s with ⟨i,j,p⟩
  cases ht : t i <;> cases p <;> simp [PositiveState,atPair,pair,ht]

/-- The reverse traversal is not another member of the positive edge orientation. -/
theorem positive_reverse_disjoint {K B : Nat} (t : Fin K → Bool) (s : State K B)
    (h : PositiveState t s) : ¬PositiveState t (atPair (fun w => t w.1) s) := by
  rcases s with ⟨i,j,p⟩
  cases ht : t i <;> cases p <;> simp [PositiveState,atPair,pair,ht] at h ⊢

/-- Literal coarse edge labels: first-axis positive edges versus second-axis
positive edges. Parallel coarse paths, if K=2, remain distinct labels. -/
abbrev CoarseEdge (K B : Nat) := Grid K B ⊕ Grid K B

def baselineEdge {K B : Nat} (hB : 0<B) (t : Fin K → Bool)
    (p : Fin B × Fin K × Bool) : CoarseEdge K B :=
  let v := baselinePoint hB t p.1 p.2.1
  if p.2.2 then .inl (v.1,signedNext hB (t v.1) v.2)
    else .inr (v.1,if t v.1 then v.2 else predecessor hB v.2)

private theorem signedNext_inverse {B : Nat} (hB : 0<B) (b : Bool) (j : Fin B) :
    signedNext hB b (signedNext hB (!b) j)=j := by
  cases b <;> simp [signedNext,successor_predecessor,predecessor_successor]

private theorem signedNext_injective {B : Nat} (hB : 0<B) (b : Bool) :
    Function.Injective (signedNext hB b) := by
  intro j k h
  have hh := congrArg (signedNext hB (!b)) h
  have hx := signedNext_inverse hB (!b) j
  have hy := signedNext_inverse hB (!b) k
  rw [Bool.not_not] at hx hy
  rw [hx,hy] at hh
  exact hh

theorem baselineEdge_surjective {K B : Nat} (hB : 0<B) (t : Fin K → Bool) :
    Function.Surjective (baselineEdge hB t) := by
  intro e
  cases e with
  | inl v =>
    let w : Grid K B := (v.1,signedNext hB (!(t v.1)) v.2)
    refine ⟨(baselineLabel hB t w,v.1,true),?_⟩
    change Sum.inl ((baselinePoint hB t (baselineLabel hB t w) w.1).1,
      signedNext hB (t (baselinePoint hB t (baselineLabel hB t w) w.1).1)
        (baselinePoint hB t (baselineLabel hB t w) w.1).2)=_
    rw [baselinePoint_label]
    simp only [w,signedNext_inverse]
  | inr v =>
    let w : Grid K B := (v.1,if t v.1 then v.2 else successor hB v.2)
    refine ⟨(baselineLabel hB t w,v.1,false),?_⟩
    change Sum.inr ((baselinePoint hB t (baselineLabel hB t w) w.1).1,
      if t (baselinePoint hB t (baselineLabel hB t w) w.1).1 then
        (baselinePoint hB t (baselineLabel hB t w) w.1).2 else
        predecessor hB (baselinePoint hB t (baselineLabel hB t w) w.1).2)=_
    rw [baselinePoint_label]
    cases ht : t v.1 <;> simp [w,ht,predecessor_successor]

theorem baselineEdge_injective {K B : Nat} (hB : 0<B) (t : Fin K → Bool) :
    Function.Injective (baselineEdge hB t) := by
  intro p v h
  rcases p with ⟨label,i,b⟩
  rcases v with ⟨label',i',b'⟩
  cases b <;> cases b'
  · have hh := Sum.inr.inj h
    have hi : i=i' := congrArg Prod.fst hh
    subst i'
    have hr := congrArg Prod.snd hh
    change (if t i then (baselinePoint hB t label i).2 else predecessor hB (baselinePoint hB t label i).2)=
      (if t i then (baselinePoint hB t label' i).2 else predecessor hB (baselinePoint hB t label' i).2) at hr
    have hrow : (baselinePoint hB t label i).2=(baselinePoint hB t label' i).2 := by
      cases ht : t i
      · simp only [ht,Bool.false_eq_true,↓reduceIte] at hr
        have hz := congrArg (successor hB) hr
        simpa only [successor_predecessor] using hz
      · simpa only [ht,↓reduceIte] using hr
    have hg : baselinePoint hB t label i=baselinePoint hB t label' i := Prod.ext rfl hrow
    have hl := congrArg (baselineLabel hB t) hg
    rw [baselineLabel_point,baselineLabel_point] at hl
    subst label'; rfl
  · cases h
  · cases h
  · have hh := Sum.inl.inj h
    have hi : i=i' := congrArg Prod.fst hh
    subst i'
    have hr := congrArg Prod.snd hh
    have hrow := signedNext_injective hB (t i) hr
    have hg : baselinePoint hB t label i=baselinePoint hB t label' i := Prod.ext rfl hrow
    have hl := congrArg (baselineLabel hB t) hg
    rw [baselineLabel_point,baselineLabel_point] at hl
    subst label'; rfl

def coarseDecode {K B : Nat} (hK : 0<K) (hB : 0<B) :
    CoarseEdge K B → Grid K B × Grid K B
  | .inl (i,j) => ((i,j),(successor hK i,j))
  | .inr (i,j) => ((i,j),(i,successor hB j))

def stateVertex {K B : Nat} (s : State K B) : Grid K B := (s.1,s.2.1)

/-- Every enumerated literal edge is the actual transition step, including
negative H orientation. No undirected edge is inferred from a state count. -/
theorem baselineEdge_step {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (p : Fin B × Fin K × Bool) :
    SameEdge (coarseDecode hK hB (baselineEdge hB t p))
      (stateVertex (baselineLoop hK hB t p.1 p.2),
       stateVertex (transition hK hB (fun w => t w.1) (baselineLoop hK hB t p.1 p.2))) := by
  rcases p with ⟨label,i,b⟩
  cases b
  · cases ht : t i
    · apply Or.inr
      simp [coarseDecode,baselineEdge,baselineLoop,stateVertex,baselinePoint,transition,atPair,pair,cross,ht,successor_predecessor]
    · apply Or.inl
      simp [coarseDecode,baselineEdge,baselineLoop,stateVertex,baselinePoint,transition,atPair,pair,cross,ht]
  · cases ht : t i <;> apply Or.inl <;>
      simp [coarseDecode,baselineEdge,baselineLoop,stateVertex,baselinePoint,signedNext,transition,atPair,pair,cross,ht]

#print axioms baselineEdge_step
#print axioms baselineEdge_injective
#print axioms baselineEdge_surjective
#print axioms transition_bijective
#print axioms drift_cyclic
#print axioms baselineLabel_invariant
#print axioms baselineLoop_next
#print axioms baselineLoop_injective
#print axioms baselineLoop_covers_positive
#print axioms positive_reverse_disjoint

end ErdePaths.AACTransition
