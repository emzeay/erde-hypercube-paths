import ErdePaths.Wiggle

namespace ErdePaths.SubdividedWiggle
open SquareLift Wiggle

/-- Actual uniformly subdivided rectangular torus coordinates: interval,
row, offset. Offset zero is an old representative. -/
abbrev FineVertex (a B s : Nat) := (Fin (2*a) × Fin B) × Fin s

def representative {a B s : Nat} (hs : 0<s) (v : Fin (2*a) × Fin B) : FineVertex a B s :=
  (v,⟨0,hs⟩)

/-- Reverse traversal of ordinary odd rows; the final staircase row goes forward. -/
def reversedRow {B : Nat} (j : Fin B) : Prop := j.val≠B-1 ∧ j.val%2≠0
instance {B : Nat} (j : Fin B) : Decidable (reversedRow j) := inferInstanceAs
  (Decidable (j.val≠B-1 ∧ j.val%2≠0))

def interiorOffset {B s : Nat} (j : Fin B) (k : Fin (s+1)) (h0 : k.val≠0) (hs : k.val≠s) : Fin s :=
  ⟨if reversedRow j then s-k.val else k.val,by
    have := k.isLt
    split <;> omega⟩

theorem interiorOffset_positive {B s : Nat} (j : Fin B) (k : Fin (s+1))
    (h0 : k.val≠0) (hs : k.val≠s) : 0<(interiorOffset j k h0 hs).val := by
  change 0<(if reversedRow j then s-k.val else k.val)
  have := k.isLt
  split <;> omega

/-- Each row replaces its first-axis arc by s steps and keeps its second-axis
arc as one step. This is an actual vertex map, with no simplicity premise. -/
def expandedVertex {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (p : Fin a × Fin B × Fin (s+1)) : FineVertex a B s :=
  if h0 : p.2.2.val=0 then representative hs (vertex ha (p.1,p.2.1,⟨0,by decide⟩))
  else if hend : p.2.2.val=s then representative hs (vertex ha (p.1,p.2.1,⟨1,by decide⟩))
  else (origin (⟨0,by decide⟩ : Fin 2) true p.1 p.2.1,
    interiorOffset p.2.1 p.2.2 h0 hend)

set_option linter.unusedSimpArgs false in
theorem expandedVertex_injective {a B s : Nat} (ha : 0<a) (hs : 0<s) :
    Function.Injective (@expandedVertex a B s ha hs) := by
  intro p q h
  rcases p with ⟨r,j,k⟩
  rcases q with ⟨r',j',k'⟩
  have hk := k.isLt; have hk' := k'.isLt
  have hsne : s≠0 := by omega
  have hv := congrArg Prod.fst h
  have ho := congrArg (fun z : FineVertex a B s => z.2.val) h
  by_cases hp0 : k.val=0 <;> by_cases hq0 : k'.val=0
  · have hv' : vertex ha (r,j,(⟨0,by decide⟩ : Fin 2))=
        vertex ha (r',j',(⟨0,by decide⟩ : Fin 2)) := by simpa [expandedVertex,hp0,hq0,representative,hsne] using hv
    have he := vertex_injective ha hv'
    apply Prod.ext
    · exact congrArg (fun z : Fin a × Fin B × Fin 2 => z.1) he
    · apply Prod.ext
      · exact congrArg (fun z => z.2.1) he
      · apply Fin.ext; change k.val=k'.val; omega
  · by_cases hqend : k'.val=s
    · have hv' : vertex ha (r,j,(⟨0,by decide⟩ : Fin 2))=
          vertex ha (r',j',(⟨1,by decide⟩ : Fin 2)) := by
        simpa [expandedVertex,hp0,hq0,hqend,representative,hsne] using hv
      have he := congrArg (fun z : Fin a × Fin B × Fin 2 => z.2.2.val) (vertex_injective ha hv')
      change (0:Nat)=1 at he
      omega
    · have hn := interiorOffset_positive j' k' hq0 hqend
      simp [expandedVertex,hp0,hq0,hqend,representative,hsne] at ho
      omega
  · by_cases hpend : k.val=s
    · have hv' : vertex ha (r,j,(⟨1,by decide⟩ : Fin 2))=
          vertex ha (r',j',(⟨0,by decide⟩ : Fin 2)) := by
        simpa [expandedVertex,hp0,hq0,hpend,representative,hsne] using hv
      have he := congrArg (fun z : Fin a × Fin B × Fin 2 => z.2.2.val) (vertex_injective ha hv')
      change (1:Nat)=0 at he
      omega
    · have hn := interiorOffset_positive j k hp0 hpend
      simp [expandedVertex,hp0,hq0,hpend,representative,hsne] at ho
      omega
  · by_cases hpend : k.val=s <;> by_cases hqend : k'.val=s
    · have hv' : vertex ha (r,j,(⟨1,by decide⟩ : Fin 2))=
          vertex ha (r',j',(⟨1,by decide⟩ : Fin 2)) := by
        simpa [expandedVertex,hp0,hq0,hpend,hqend,representative,hsne] using hv
      have he := vertex_injective ha hv'
      apply Prod.ext
      · exact congrArg (fun z : Fin a × Fin B × Fin 2 => z.1) he
      · apply Prod.ext
        · exact congrArg (fun z => z.2.1) he
        · apply Fin.ext; change k.val=k'.val; omega
    · have hn := interiorOffset_positive j' k' hq0 hqend
      simp [expandedVertex,hp0,hq0,hpend,hqend,representative,hsne] at ho
      omega
    · have hn := interiorOffset_positive j k hp0 hpend
      simp [expandedVertex,hp0,hq0,hpend,hqend,representative,hsne] at ho
      omega
    · have hv' : origin (⟨0,by decide⟩ : Fin 2) true r j=
          origin (⟨0,by decide⟩ : Fin 2) true r' j' := by
        simpa [expandedVertex,hp0,hq0,hpend,hqend] using hv
      have he : ((⟨0,by decide⟩ : Fin 2),r,j)=((⟨0,by decide⟩ : Fin 2),r',j') :=
        origin_injective true hv'
      have hr : r=r' := congrArg (fun z => z.2.1) he
      have hj : j=j' := congrArg (fun z => z.2.2) he
      subst r'; subst j'
      have hoff : (interiorOffset j k hp0 hpend).val=(interiorOffset j k' hq0 hqend).val := by
        simpa [expandedVertex,hp0,hq0,hpend,hqend] using ho
      have heq : k=k' := by
        apply Fin.ext
        change (if reversedRow j then s-k.val else k.val)=(if reversedRow j then s-k'.val else k'.val) at hoff
        by_cases hrev : reversedRow j <;> simp only [hrev,ite_true,ite_false] at hoff <;> omega
      subst k'
      rfl

/-- Translation by one original first-axis interval (s fine edges). -/
def fineShift {a B s : Nat} (ha : 0<a) (v : FineVertex a B s) : FineVertex a B s :=
  ((successor (show 0<2*a by omega) v.1.1,v.1.2),v.2)

def translatedExpandedVertex {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (p : Fin a × Fin B × Fin (s+1)) : FineVertex a B s := fineShift ha (expandedVertex ha hs p)

theorem fineShift_injective {a B s : Nat} (ha : 0<a) : Function.Injective (@fineShift a B s ha) := by
  intro u v h
  have hx := congrArg (fun z : FineVertex a B s => z.1.1) h
  have hy := congrArg (fun z : FineVertex a B s => z.1.2) h
  have hk := congrArg (fun z : FineVertex a B s => z.2) h
  have he := congrArg (predecessor (show 0<2*a by omega)) hx
  simp only [fineShift,predecessor_successor] at he hy hk
  exact Prod.ext (Prod.ext he hy) hk

theorem translatedExpandedVertex_injective {a B s : Nat} (ha : 0<a) (hs : 0<s) :
    Function.Injective (@translatedExpandedVertex a B s ha hs) := by
  intro p q h
  exact expandedVertex_injective ha hs (fineShift_injective ha h)

/-- Numeric scalar index for the constant-sized row macro. -/
def expandedCoordinates {a B s : Nat} (hB : 0<B)
    (t : Fin (a*(B*(s+1)))) : Fin a × Fin B × Fin (s+1) :=
  (⟨t.val/(B*(s+1)),Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using t.isLt)⟩,
   ⟨(t.val%(B*(s+1)))/(s+1),Nat.div_lt_of_lt_mul (by
      simpa only [Nat.mul_comm] using Nat.mod_lt t.val (Nat.mul_pos hB (by omega)))⟩,
   ⟨t.val%(s+1),Nat.mod_lt _ (by omega)⟩)

theorem expandedCoordinates_injective {a B s : Nat} (hB : 0<B) :
    Function.Injective (@expandedCoordinates a B s hB) := by
  intro u v h
  have hq := congrArg (fun z : Fin a × Fin B × Fin (s+1) => z.1.val) h
  have hj := congrArg (fun z : Fin a × Fin B × Fin (s+1) => z.2.1.val) h
  have hk := congrArg (fun z : Fin a × Fin B × Fin (s+1) => z.2.2.val) h
  change u.val/(B*(s+1))=v.val/(B*(s+1)) at hq
  change (u.val%(B*(s+1)))/(s+1)=(v.val%(B*(s+1)))/(s+1) at hj
  change u.val%(s+1)=v.val%(s+1) at hk
  have hmu : (u.val%(B*(s+1)))%(s+1)=u.val%(s+1) := Nat.mod_mod_of_dvd _ ⟨B,Nat.mul_comm _ _⟩
  have hmv : (v.val%(B*(s+1)))%(s+1)=v.val%(s+1) := Nat.mod_mod_of_dvd _ ⟨B,Nat.mul_comm _ _⟩
  have hu := Nat.div_add_mod (u.val%(B*(s+1))) (s+1)
  have hv := Nat.div_add_mod (v.val%(B*(s+1))) (s+1)
  rw [hmu,hj,hk] at hu
  rw [hmv] at hv
  have hm : u.val%(B*(s+1))=v.val%(B*(s+1)) := by omega
  have hu' := Nat.div_add_mod u.val (B*(s+1))
  have hv' := Nat.div_add_mod v.val (B*(s+1))
  rw [hq,hm] at hu'
  exact Fin.ext (by omega)

def expandedCycle {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (t : Fin (a*(B*(s+1)))) : FineVertex a B s := expandedVertex ha hs (expandedCoordinates hB t)

def translatedExpandedCycle {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (t : Fin (a*(B*(s+1)))) : FineVertex a B s := translatedExpandedVertex ha hs (expandedCoordinates hB t)

theorem expandedCycle_injective {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) :
    Function.Injective (@expandedCycle a B s ha hB hs) := by
  intro u v h
  exact expandedCoordinates_injective hB (expandedVertex_injective ha hs h)

theorem translatedExpandedCycle_injective {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) :
    Function.Injective (@translatedExpandedCycle a B s ha hB hs) := by
  intro u v h
  exact expandedCoordinates_injective hB (translatedExpandedVertex_injective ha hs h)

theorem expandedCycle_list_nodup {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) :
    (List.ofFn (expandedCycle ha hB hs)).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  simp only [List.getElem_ofFn] at he
  exact congrArg Fin.val (expandedCycle_injective ha hB hs he)

theorem expandedCycle_length {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) :
    (List.ofFn (expandedCycle ha hB hs)).length=a*B*(s+1) := by
  simp only [List.length_ofFn,Nat.mul_assoc]

theorem expanded_internal_source {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (p : Fin a × Fin B × Fin (s+1))
    (h : (expandedVertex ha hs p).2.val≠0) :
    (expandedVertex ha hs p).1=origin (⟨0,by decide⟩ : Fin 2) true p.1 p.2.1 := by
  by_cases h0 : p.2.2.val=0
  · simp [expandedVertex,h0,representative] at h
  · by_cases hend : p.2.2.val=s
    · simp [expandedVertex,hend,representative,show s≠0 by omega] at h
    · simp [expandedVertex,h0,hend]

theorem translated_internal_source {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (p : Fin a × Fin B × Fin (s+1))
    (h : (translatedExpandedVertex ha hs p).2.val≠0) :
    (translatedExpandedVertex ha hs p).1=
      origin (⟨1,by decide⟩ : Fin 2) true (translatedBlock ha true p.1 p.2.1) p.2.1 := by
  have h0 : (expandedVertex ha hs p).2.val≠0 := h
  have hc := expanded_internal_source ha hs p h0
  change shiftVertex ha (expandedVertex ha hs p).1=_
  rw [hc]
  exact origin_translate ha true p.1 p.2.1

/-- Every interior vertex on a color-zero first-axis interval is absent
from the entire explicit color-one subdivided tour. -/
theorem interior_exclusive_zero {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (r : Fin a) (j : Fin B) (k : Fin s) (hk : k.val≠0)
    (p : Fin a × Fin B × Fin (s+1)) :
    translatedExpandedVertex ha hs p≠(origin (⟨0,by decide⟩ : Fin 2) true r j,k) := by
  intro h
  have ho := congrArg (fun z : FineVertex a B s => z.2.val) h
  have hnonzero : (translatedExpandedVertex ha hs p).2.val≠0 := by
    change (translatedExpandedVertex ha hs p).2.val=k.val at ho
    rw [ho]; exact hk
  have hc := translated_internal_source ha hs p hnonzero
  have hv := congrArg Prod.fst h
  rw [hc] at hv
  have he : ((⟨1,by decide⟩ : Fin 2),translatedBlock ha true p.1 p.2.1,p.2.1)=
      ((⟨0,by decide⟩ : Fin 2),r,j) := origin_injective true hv
  have hb := congrArg (fun z : Fin 2 × Fin a × Fin B => z.1.val) he
  change (1:Nat)=0 at hb
  omega

/-- Every interior vertex on a color-one first-axis interval is absent
from the entire explicit color-zero subdivided tour. -/
theorem interior_exclusive_one {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (r : Fin a) (j : Fin B) (k : Fin s) (hk : k.val≠0)
    (p : Fin a × Fin B × Fin (s+1)) :
    expandedVertex ha hs p≠(origin (⟨1,by decide⟩ : Fin 2) true r j,k) := by
  intro h
  have ho := congrArg (fun z : FineVertex a B s => z.2.val) h
  have hnonzero : (expandedVertex ha hs p).2.val≠0 := by
    change (expandedVertex ha hs p).2.val=k.val at ho
    rw [ho]; exact hk
  have hc := expanded_internal_source ha hs p hnonzero
  have hv := congrArg Prod.fst h
  rw [hc] at hv
  have he : ((⟨0,by decide⟩ : Fin 2),p.1,p.2.1)=
      ((⟨1,by decide⟩ : Fin 2),r,j) := origin_injective true hv
  have hb := congrArg (fun z : Fin 2 × Fin a × Fin B => z.1.val) he
  change (0:Nat)=1 at hb
  omega

/-- Actual successor along one uniformly subdivided first-axis interval. -/
def fineNext {a B s : Nat} (ha : 0<a) (hs : 0<s) (v : FineVertex a B s) : FineVertex a B s :=
  if hk : v.2.val+1<s then (v.1,⟨v.2.val+1,hk⟩)
  else ((successor (show 0<2*a by omega) v.1.1,v.1.2),⟨0,hs⟩)

/-- Exactly the edges of a uniformly first-axis subdivided torus: all fine
first-axis edges, and second-axis edges only at representative offset zero. -/
def FineAdjacent {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (u v : FineVertex a B s) : Prop :=
  fineNext ha hs u=v ∨ fineNext ha hs v=u ∨
  (u.2.val=0 ∧ v.2.val=0 ∧ u.1.1=v.1.1 ∧
    (successor hB u.1.2=v.1.2 ∨ successor hB v.1.2=u.1.2))

/-- A row-zero anchor and its physically nearest first-axis neighbors. -/
def anchor {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) : FineVertex a B s :=
  ((⟨0,by omega⟩,⟨0,hB⟩),⟨0,hs⟩)

def rightNeighbor {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 2≤s) : FineVertex a B s :=
  (origin (⟨0,by decide⟩ : Fin 2) true ⟨0,ha⟩ ⟨0,hB⟩,⟨1,by omega⟩)

def leftNeighbor {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 2≤s) : FineVertex a B s :=
  (origin (⟨1,by decide⟩ : Fin 2) true ⟨a-1,by omega⟩ ⟨0,hB⟩,⟨s-1,by omega⟩)

set_option linter.unusedSimpArgs false in
theorem rightNeighbor_occurs {a B s : Nat} (ha : 0<a) (hB : 4≤B) (hs : 2≤s) :
    expandedVertex ha (by omega) (⟨0,ha⟩,⟨0,by omega⟩,⟨1,by omega⟩)=
      rightNeighbor (B := B) ha (by omega) hs := by
  have hrow : (0:Nat)≠B-1 := by omega
  simp [expandedVertex,rightNeighbor,interiorOffset,reversedRow,hrow,show (1:Nat)≠s by omega]

theorem rightNeighbor_exclusive {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 2≤s)
    (p : Fin a × Fin B × Fin (s+1)) :
    translatedExpandedVertex ha (by omega) p≠rightNeighbor (B := B) ha hB hs :=
  interior_exclusive_zero ha (by omega) _ _ _ (by change (1:Nat)≠0; omega) p

set_option linter.unusedSimpArgs false in
theorem leftNeighbor_occurs {a B s : Nat} (ha : 0<a) (hB : 4≤B) (hs : 2≤s) :
    translatedExpandedVertex ha (by omega) (⟨a-1,by omega⟩,⟨0,by omega⟩,⟨s-1,by omega⟩)=
      leftNeighbor (B := B) ha (by omega) hs := by
  have hrow : (0:Nat)≠B-1 := by omega
  have hk0 : s-1≠0 := by omega
  have hks : s-1≠s := by omega
  simp [translatedExpandedVertex,expandedVertex,leftNeighbor,interiorOffset,reversedRow,
    fineShift,origin,pairEncode,Fin.rev,successor,hrow,hk0,hks]
  exact Nat.mod_eq_of_lt (by omega)

theorem leftNeighbor_exclusive {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 2≤s)
    (p : Fin a × Fin B × Fin (s+1)) :
    expandedVertex ha (by omega) p≠leftNeighbor (B := B) ha hB hs :=
  interior_exclusive_one ha (by omega) _ _ _ (by change s-1≠0; omega) p

theorem rightNeighbor_adjacent {a B s : Nat} (ha : 0<a) (hB : 4≤B) (hs : 2≤s) :
    FineAdjacent (B := B) ha (by omega) (by omega) (anchor (B := B) ha (by omega) (by omega))
      (rightNeighbor (B := B) ha (by omega) hs) := by
  apply Or.inl
  have hrow : (0:Nat)≠B-1 := by omega
  simp [fineNext,anchor,rightNeighbor,origin,pairEncode,hrow,show (1:Nat)<s by omega]

theorem leftNeighbor_adjacent {a B s : Nat} (ha : 0<a) (hB : 4≤B) (hs : 2≤s) :
    FineAdjacent (B := B) ha (by omega) (by omega) (anchor (B := B) ha (by omega) (by omega))
      (leftNeighbor (B := B) ha (by omega) hs) := by
  apply Or.inr; apply Or.inl
  have hrow : (0:Nat)≠B-1 := by omega
  have hk : ¬s-1+1<s := by omega
  simp [fineNext,anchor,leftNeighbor,origin,pairEncode,successor,hrow,hk]
  have he : 2*(a-1)+1+1=2*a := by omega
  simp [he]

theorem anchor_occurs_zero {a B s : Nat} (ha : 0<a) (hB : 4≤B) (hs : 0<s) :
    expandedVertex ha hs (⟨0,ha⟩,⟨0,by omega⟩,⟨0,by omega⟩)=
      anchor (B := B) ha (by omega) hs := by
  have hrow : (0:Nat)≠B-1 := by omega
  simp [expandedVertex,representative,vertex,rowMap,rowParity,pairEncode,anchor,hrow]

theorem anchor_occurs_one {a B s : Nat} (ha : 0<a) (hB : 4≤B) (hs : 0<s) :
    translatedExpandedVertex ha hs (⟨a-1,by omega⟩,⟨0,by omega⟩,⟨s,by omega⟩)=
      anchor (B := B) ha (by omega) hs := by
  have hrow : (0:Nat)≠B-1 := by omega
  have hsne : s≠0 := by omega
  simp [translatedExpandedVertex,expandedVertex,representative,vertex,rowMap,rowParity,
    pairEncode,anchor,fineShift,successor,hrow,hsne]
  have he : 2*(a-1)+1+1=2*a := by omega
  simp [he]

/-- The actual s-edge subdivision of one first-axis interval. -/
def intervalVertex {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (u : Fin (2*a) × Fin B) (rev : Bool) (k : Fin (s+1)) : FineVertex a B s :=
  if rev then
    if hk : k.val=0 then representative hs (successor (show 0<2*a by omega) u.1,u.2)
    else (u,⟨s-k.val,by have := k.isLt; omega⟩)
  else if hk : k.val<s then (u,⟨k.val,hk⟩)
    else representative hs (successor (show 0<2*a by omega) u.1,u.2)

set_option linter.unusedSimpArgs false in
theorem intervalVertex_step {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (u : Fin (2*a) × Fin B) (rev : Bool) (k : Fin s) :
    FineAdjacent ha hB hs (intervalVertex ha hs u rev k.castSucc)
      (intervalVertex ha hs u rev k.succ) := by
  have hk := k.isLt
  cases rev
  · apply Or.inl
    by_cases hknext : k.val+1<s
    · simp [intervalVertex,fineNext,hknext,hk,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ]
    · have hlast : k.val+1=s := by omega
      simp [intervalVertex,fineNext,hknext,hk,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,representative]
  · apply Or.inr; apply Or.inl
    by_cases hk0 : k.val=0
    · have hlast : s-(k.val+1)+1=s := by omega
      have hn : ¬s-(k.val+1)+1<s := by omega
      simp [intervalVertex,fineNext,representative,hk0,hn,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ]
      have hsback : s-1+1=s := by omega
      simp [hsback]
    · have hn : s-(k.val+1)+1<s := by omega
      simp [intervalVertex,fineNext,representative,hk0,hn,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ]
      omega

set_option linter.unusedSimpArgs false in
/-- Explicit first-axis interval endpoints of the checked two-wiggle row. -/
theorem row_endpoints {a B : Nat} (ha : 0<a) (j : Fin B) (r : Fin a) :
    let u := origin (⟨0,by decide⟩ : Fin 2) true r j
    if reversedRow j then
      vertex ha (r,j,(⟨0,by decide⟩ : Fin 2))=(successor (show 0<2*a by omega) u.1,u.2) ∧
      vertex ha (r,j,(⟨1,by decide⟩ : Fin 2))=u
    else
      vertex ha (r,j,(⟨0,by decide⟩ : Fin 2))=u ∧
      vertex ha (r,j,(⟨1,by decide⟩ : Fin 2))=(successor (show 0<2*a by omega) u.1,u.2) := by
  have hr := r.isLt
  have hmod : (2*r.val+1)%(2*a)=2*r.val+1 := Nat.mod_eq_of_lt (by omega)
  by_cases hjlast : j.val=B-1
  · simp [vertex,rowMap,origin,pairEncode,rowParity,reversedRow,hjlast,Fin.rev,successor,hmod]
  · by_cases hjpar : j.val%2=0
    · simp [vertex,rowMap,origin,pairEncode,rowParity,reversedRow,hjlast,hjpar,Fin.rev,successor,hmod]
    · simp [vertex,rowMap,origin,pairEncode,rowParity,reversedRow,hjlast,hjpar,Fin.rev,successor,hmod]

set_option linter.unusedSimpArgs false in
theorem expandedVertex_interval {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (r : Fin a) (j : Fin B) (k : Fin (s+1)) :
    expandedVertex ha hs (r,j,k)=intervalVertex ha hs
      (origin (⟨0,by decide⟩ : Fin 2) true r j) (decide (reversedRow j)) k := by
  have he := row_endpoints ha j r
  have hk := k.isLt
  by_cases hrev : reversedRow j
  · simp only [hrev,ite_true] at he
    by_cases hk0 : k.val=0
    · simp [expandedVertex,intervalVertex,hrev,hk0]
      exact congrArg (representative hs) he.1
    · by_cases hkend : k.val=s
      · simp [expandedVertex,intervalVertex,hrev,hk0,hkend,representative,show s≠0 by omega]
        exact he.2
      · simp [expandedVertex,intervalVertex,interiorOffset,hrev,hk0,hkend]
  · simp only [hrev,ite_false] at he
    by_cases hk0 : k.val=0
    · simp [expandedVertex,intervalVertex,hrev,hk0,representative,hs]
      exact he.1
    · by_cases hkend : k.val=s
      · simp [expandedVertex,intervalVertex,hrev,hk0,hkend,representative,show s≠0 by omega]
        exact he.2
      · have hklt : k.val<s := by omega
        simp [expandedVertex,intervalVertex,interiorOffset,hrev,hk0,hkend,hklt]

theorem expandedVertex_firstAxis_step {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (r : Fin a) (j : Fin B) (k : Fin s) :
    FineAdjacent ha hB hs (expandedVertex ha hs (r,j,k.castSucc))
      (expandedVertex ha hs (r,j,k.succ)) := by
  rw [expandedVertex_interval,expandedVertex_interval]
  exact intervalVertex_step ha hB hs _ _ k

theorem representative_secondAxis_step {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (u v w : Fin (2*a) × Fin B)
    (h : SameEdge (u,v) (axisEdge (show 0<2*a by omega) hB false w)) :
    FineAdjacent ha hB hs (representative hs u) (representative hs v) := by
  rcases h with h | h
  · have hu := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    simp only [axisEdge,Bool.false_eq_true,ite_false] at hu hv
    rw [hu,hv]
    exact Or.inr (Or.inr ⟨rfl,rfl,rfl,Or.inl rfl⟩)
  · have hu := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    simp only [axisEdge,Bool.false_eq_true,ite_false] at hu hv
    rw [hu,hv]
    exact Or.inr (Or.inr ⟨rfl,rfl,rfl,Or.inr rfl⟩)

/-- Constant-sized macro successor, including both row and block wraps. -/
def expandedNext {a B s : Nat} (ha : 0<a) (hB : 0<B)
    (p : Fin a × Fin B × Fin (s+1)) : Fin a × Fin B × Fin (s+1) :=
  if hk : p.2.2.val<s then (p.1,p.2.1,⟨p.2.2.val+1,by omega⟩)
  else if hj : p.2.1.val+1<B then (p.1,⟨p.2.1.val+1,hj⟩,⟨0,by omega⟩)
  else (successor ha p.1,⟨0,hB⟩,⟨0,by omega⟩)

set_option linter.unusedSimpArgs false in
theorem expandedVertex_secondAxis_step {a B s : Nat} (ha : 2≤a) (hB : 4≤B)
    (heven : B%2=0) (hs : 0<s) (r : Fin a) (j : Fin B) :
    FineAdjacent (show 0<a by omega) (show 0<B by omega) hs
      (expandedVertex (by omega) hs (r,j,⟨s,by omega⟩))
      (expandedVertex (by omega) hs (expandedNext (by omega) (by omega) (r,j,⟨s,by omega⟩))) := by
  have hsne : s≠0 := by omega
  have h := coordinate_step ha hB heven (r,j,(⟨1,by decide⟩ : Fin 2))
  have hj := j.isLt
  by_cases hjnext : j.val+1<B
  · simp [coordinateNext,coordinateLabel,hjnext] at h
    have hh := representative_secondAxis_step (show 0<a by omega) (show 0<B by omega) hs _ _ _ h
    simpa [expandedVertex,expandedNext,hjnext,hsne] using hh
  · simp [coordinateNext,coordinateLabel,hjnext] at h
    have hh := representative_secondAxis_step (show 0<a by omega) (show 0<B by omega) hs _ _ _ h
    simpa [expandedVertex,expandedNext,hjnext,hsne] using hh

set_option linter.unusedSimpArgs false in
theorem expandedVertex_adjacent {a B s : Nat} (ha : 2≤a) (hB : 4≤B)
    (heven : B%2=0) (hs : 0<s) (p : Fin a × Fin B × Fin (s+1)) :
    FineAdjacent (show 0<a by omega) (show 0<B by omega) hs
      (expandedVertex (by omega) hs p)
      (expandedVertex (by omega) hs (expandedNext (by omega) (by omega) p)) := by
  by_cases hk : p.2.2.val<s
  · have hh := expandedVertex_firstAxis_step (show 0<a by omega) (show 0<B by omega) hs
      p.1 p.2.1 ⟨p.2.2.val,hk⟩
    have he : (⟨p.2.2.val,hk⟩ : Fin s).castSucc=p.2.2 := Fin.ext rfl
    rw [he] at hh
    simpa [expandedNext,hk,Fin.succ] using hh
  · have hlast : p.2.2.val=s := by have := p.2.2.isLt; omega
    have he : p.2.2=(⟨s,by omega⟩ : Fin (s+1)) := Fin.ext hlast
    have hh := expandedVertex_secondAxis_step ha hB heven hs p.1 p.2.1
    simpa only [←he] using hh

def expandedIndex {a B s : Nat} (p : Fin a × Fin B × Fin (s+1)) : Fin (a*(B*(s+1))) :=
  ⟨(B*(s+1))*p.1.val+(p.2.1.val*(s+1)+p.2.2.val),by
    have hi : p.2.1.val*(s+1)+p.2.2.val<B*(s+1) := by
      have hj := Nat.mul_le_mul_right (s+1) (show p.2.1.val+1≤B by have := p.2.1.isLt; omega)
      rw [Nat.add_mul] at hj
      have := p.2.2.isLt
      omega
    have hr := Nat.mul_le_mul_right (B*(s+1)) (show p.1.val+1≤a by have := p.1.isLt; omega)
    rw [Nat.add_mul,Nat.mul_comm p.1.val] at hr
    omega⟩

theorem expandedIndex_inverse {a B s : Nat} (hB : 0<B) (p : Fin a × Fin B × Fin (s+1)) :
    expandedCoordinates hB (expandedIndex p)=p := by
  have hi : p.2.1.val*(s+1)+p.2.2.val<B*(s+1) := by
    have hj := Nat.mul_le_mul_right (s+1) (show p.2.1.val+1≤B by have := p.2.1.isLt; omega)
    rw [Nat.add_mul] at hj
    have := p.2.2.isLt
    omega
  apply Prod.ext
  · apply Fin.ext
    simp only [expandedCoordinates,expandedIndex,Nat.mul_add_div (Nat.mul_pos hB (show 0<s+1 by omega)),
      Nat.div_eq_of_lt hi,Nat.add_zero]
  · apply Prod.ext <;> apply Fin.ext
    · simp only [expandedCoordinates,expandedIndex,Nat.mul_add_mod,Nat.mod_eq_of_lt hi]
      rw [Nat.mul_comm p.2.1.val,Nat.mul_add_div (show 0<s+1 by omega),Nat.div_eq_of_lt p.2.2.isLt,Nat.add_zero]
    · simp only [expandedCoordinates,expandedIndex]
      have he : (B*(s+1))*p.1.val=(s+1)*(B*p.1.val) := by rw [Nat.mul_comm B,Nat.mul_assoc]
      rw [he,Nat.mul_add_mod,Nat.mul_comm p.2.1.val,Nat.mul_add_mod,Nat.mod_eq_of_lt p.2.2.isLt]

theorem expandedIndex_reverse {a B s : Nat} (hB : 0<B) (t : Fin (a*(B*(s+1)))) :
    expandedIndex (expandedCoordinates hB t)=t := by
  apply expandedCoordinates_injective hB
  exact expandedIndex_inverse hB _

set_option linter.unusedSimpArgs false in
theorem expandedIndex_next {a B s : Nat} (ha : 0<a) (hB : 0<B)
    (p : Fin a × Fin B × Fin (s+1)) :
    expandedIndex (expandedNext ha hB p)=
      successor (Nat.mul_pos ha (Nat.mul_pos hB (show 0<s+1 by omega))) (expandedIndex p) := by
  rcases p with ⟨r,j,k⟩
  have hr := r.isLt; have hj := j.isLt; have hk := k.isLt
  have hbound := Nat.mul_le_mul_right (B*(s+1)) (show r.val+1≤a by omega)
  rw [Nat.add_mul,Nat.mul_comm r.val] at hbound
  have jbound := Nat.mul_le_mul_right (s+1) (show j.val+1≤B by omega)
  rw [Nat.add_mul] at jbound
  by_cases hkl : k.val<s
  · apply Fin.ext
    simp [expandedIndex,expandedNext,hkl,successor]
    exact (Nat.mod_eq_of_lt (show (B*(s+1))*r.val+(j.val*(s+1)+k.val)+1<a*(B*(s+1)) by omega)).symm
  · have hkend : k.val=s := by omega
    by_cases hjnext : j.val+1<B
    · have jlt := Nat.mul_lt_mul_of_pos_right hjnext (show 0<s+1 by omega)
      rw [Nat.add_mul] at jlt
      apply Fin.ext
      simp [expandedIndex,expandedNext,hkl,hjnext,successor]
      have hm : ((B*(s+1))*r.val+(j.val*(s+1)+k.val)+1)%(a*(B*(s+1)))=
          (B*(s+1))*r.val+(j.val*(s+1)+k.val)+1 := Nat.mod_eq_of_lt (by omega)
      rw [hm,Nat.add_mul]
      omega
    · have hjend : j.val+1=B := by omega
      have jendmul := congrArg (fun n => n*(s+1)) hjend
      rw [Nat.add_mul] at jendmul
      by_cases hrnext : r.val+1<a
      · have rlt := Nat.mul_lt_mul_of_pos_right hrnext (Nat.mul_pos hB (show 0<s+1 by omega))
        rw [Nat.add_mul,Nat.mul_comm r.val] at rlt
        apply Fin.ext
        simp [expandedIndex,expandedNext,hkl,hjnext,successor,Nat.mod_eq_of_lt hrnext]
        have hm : ((B*(s+1))*r.val+(j.val*(s+1)+k.val)+1)%(a*(B*(s+1)))=
            (B*(s+1))*r.val+(j.val*(s+1)+k.val)+1 := Nat.mod_eq_of_lt (by omega)
        rw [hm,Nat.mul_add]
        omega
      · have hrend : r.val+1=a := by omega
        have rendmul := congrArg (fun n => n*(B*(s+1))) hrend
        rw [Nat.add_mul,Nat.mul_comm r.val] at rendmul
        apply Fin.ext
        simp [expandedIndex,expandedNext,hkl,hjnext,successor,hrend]
        have he : (B*(s+1))*r.val+(j.val*(s+1)+k.val)+1=a*(B*(s+1)) := by omega
        simp [he]

theorem expandedCoordinates_next {a B s : Nat} (ha : 0<a) (hB : 0<B)
    (t : Fin (a*(B*(s+1)))) :
    expandedCoordinates hB (successor (Nat.mul_pos ha (Nat.mul_pos hB (show 0<s+1 by omega))) t)=
      expandedNext ha hB (expandedCoordinates hB t) := by
  rw [←expandedIndex_reverse hB t,←expandedIndex_next ha hB]
  simp only [expandedIndex_inverse]

theorem expandedCycle_adjacent {a B s : Nat} (ha : 2≤a) (hB : 4≤B)
    (heven : B%2=0) (hs : 0<s) (t : Fin (a*(B*(s+1)))) :
    FineAdjacent (show 0<a by omega) (show 0<B by omega) hs
      (expandedCycle (by omega) (by omega) hs t)
      (expandedCycle (by omega) (by omega) hs
        (successor (Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) t)) := by
  unfold expandedCycle
  rw [expandedCoordinates_next (show 0<a by omega) (show 0<B by omega)]
  exact expandedVertex_adjacent ha hB heven hs _

theorem fineShift_next {a B s : Nat} (ha : 0<a) (hs : 0<s) (u : FineVertex a B s) :
    fineNext ha hs (fineShift ha u)=fineShift ha (fineNext ha hs u) := by
  unfold fineNext fineShift
  split <;> rfl

theorem fineShift_adjacent {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    {u v : FineVertex a B s} (h : FineAdjacent ha hB hs u v) :
    FineAdjacent ha hB hs (fineShift ha u) (fineShift ha v) := by
  rcases h with h | h | ⟨hu,hv,hx,hy⟩
  · apply Or.inl
    rw [fineShift_next,h]
  · apply Or.inr; apply Or.inl
    rw [fineShift_next,h]
  · exact Or.inr (Or.inr ⟨hu,hv,congrArg (successor (show 0<2*a by omega)) hx,hy⟩)

theorem translatedExpandedCycle_adjacent {a B s : Nat} (ha : 2≤a) (hB : 4≤B)
    (heven : B%2=0) (hs : 0<s) (t : Fin (a*(B*(s+1)))) :
    FineAdjacent (show 0<a by omega) (show 0<B by omega) hs
      (translatedExpandedCycle (by omega) (by omega) hs t)
      (translatedExpandedCycle (by omega) (by omega) hs
        (successor (Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) t)) :=
  fineShift_adjacent _ _ _ (expandedCycle_adjacent ha hB heven hs t)

theorem translatedExpandedCycle_list_nodup {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) :
    (List.ofFn (translatedExpandedCycle ha hB hs)).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  simp only [List.getElem_ofFn] at he
  exact congrArg Fin.val (translatedExpandedCycle_injective ha hB hs he)

theorem subdividedCycle_equal_lengths {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) :
    (List.ofFn (expandedCycle ha hB hs)).length=(2*a)*B*(s+1)/2 ∧
    (List.ofFn (translatedExpandedCycle ha hB hs)).length=(2*a)*B*(s+1)/2 := by
  have hc := uniform_subdivision_count a B s
  have hl : a*(B*(s+1))=(2*a)*B*(s+1)/2 := by
    rw [←hc]
    simp only [Nat.mul_add,Nat.mul_one,Nat.mul_assoc]
  exact ⟨List.length_ofFn.trans hl,List.length_ofFn.trans hl⟩

def fineIntervalEdge {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (u : Fin (2*a) × Fin B) (k : Fin s) := ((u,k),fineNext ha hs (u,k))

def fineRepresentativeEdge {a B s : Nat} (hs : 0<s)
    (e : (Fin (2*a) × Fin B) × (Fin (2*a) × Fin B)) :=
  (representative hs e.1,representative hs e.2)

set_option linter.unusedSimpArgs false in
theorem intervalVertex_decodes {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (u : Fin (2*a) × Fin B) (rev : Bool) (k : Fin s) :
    SameEdge (intervalVertex ha hs u rev k.castSucc,intervalVertex ha hs u rev k.succ)
      (fineIntervalEdge ha hs u (if rev then k.rev else k)) := by
  have hk := k.isLt
  cases rev
  · apply Or.inl
    by_cases hn : k.val+1<s
    · simp [intervalVertex,fineIntervalEdge,fineNext,hn,hk,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ]
    · simp [intervalVertex,fineIntervalEdge,fineNext,hn,hk,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,representative]
  · apply Or.inr
    by_cases hk0 : k.val=0
    · have hn : ¬s-(k.val+1)+1<s := by omega
      have hsback : s-1+1=s := by omega
      simp [intervalVertex,fineIntervalEdge,fineNext,representative,hk0,hn,Fin.castSucc,
        Fin.castAdd,Fin.castLE,Fin.succ,Fin.rev,hsback]
    · have hn : s-(k.val+1)+1<s := by omega
      have hn' : s-(k.val+1)+1≠0 := by omega
      simp [intervalVertex,fineIntervalEdge,fineNext,representative,hk0,hn,Fin.castSucc,
        Fin.castAdd,Fin.castLE,Fin.succ,Fin.rev]
      omega

theorem expanded_macro_decodes {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (r : Fin a) (j : Fin B) (k : Fin s) :
    SameEdge (expandedVertex ha hs (r,j,k.castSucc),expandedVertex ha hs (r,j,k.succ))
      (fineIntervalEdge ha hs (origin (⟨0,by decide⟩ : Fin 2) true r j)
        (if reversedRow j then k.rev else k)) := by
  rw [expandedVertex_interval,expandedVertex_interval]
  have h := intervalVertex_decodes ha hs (origin (⟨0,by decide⟩ : Fin 2) true r j)
    (decide (reversedRow j)) k
  by_cases hr : reversedRow j <;> simpa [hr] using h

/-- Every fine edge of every color-zero first-axis interval occurs in the
actual explicit expanded coordinate tour. -/
theorem expanded_covers_firstAxis {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (r : Fin a) (j : Fin B) (k : Fin s) :
    ∃ p, SameEdge (expandedVertex ha hs p,expandedVertex ha hs (expandedNext ha hB p))
      (fineIntervalEdge ha hs (origin (⟨0,by decide⟩ : Fin 2) true r j) k) := by
  let q : Fin s := if reversedRow j then k.rev else k
  have hq : (if reversedRow j then q.rev else q)=k := by
    by_cases hr : reversedRow j <;> simp [q,hr]
  refine ⟨(r,j,q.castSucc),?_⟩
  have h := expanded_macro_decodes ha hs r j q
  rw [hq] at h
  simpa [expandedNext,q.isLt,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ] using h

def fineShiftEdge {a B s : Nat} (ha : 0<a) (e : FineVertex a B s × FineVertex a B s) :=
  (fineShift ha e.1,fineShift ha e.2)

theorem map_sameEdge {V W : Type} (f : V → W) {e d : V × V} (h : SameEdge e d) :
    SameEdge (f e.1,f e.2) (f d.1,f d.2) := by
  rcases h with h | h
  · exact Or.inl (congrArg (fun z => (f z.1,f z.2)) h)
  · apply Or.inr
    rw [h]

theorem fineIntervalEdge_translate {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (r : Fin a) (j : Fin B) (k : Fin s) :
    fineShiftEdge ha (fineIntervalEdge ha hs (origin (⟨0,by decide⟩ : Fin 2) true r j) k)=
      fineIntervalEdge ha hs (origin (⟨1,by decide⟩ : Fin 2) true (translatedBlock ha true r j) j) k := by
  have hu : fineShift ha (origin (⟨0,by decide⟩ : Fin 2) true r j,k)=
      (origin (⟨1,by decide⟩ : Fin 2) true (translatedBlock ha true r j) j,k) :=
    Prod.ext (origin_translate ha true r j) rfl
  unfold fineShiftEdge fineIntervalEdge
  rw [←fineShift_next,hu]

theorem translated_covers_firstAxis {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (r : Fin a) (j : Fin B) (k : Fin s) :
    ∃ p, SameEdge (translatedExpandedVertex ha hs p,translatedExpandedVertex ha hs (expandedNext ha hB p))
      (fineIntervalEdge ha hs (origin (⟨1,by decide⟩ : Fin 2) true r j) k) := by
  obtain ⟨r',hr⟩ := translatedBlock_surjective ha true j r
  change translatedBlock ha true r' j=r at hr
  obtain ⟨p,hp⟩ := expanded_covers_firstAxis ha hB hs r' j k
  refine ⟨p,?_⟩
  have hh := map_sameEdge (fineShift ha) hp
  change SameEdge _ (fineShiftEdge ha _) at hh
  rw [fineIntervalEdge_translate,hr] at hh
  exact hh

set_option linter.unusedSimpArgs false in
theorem expanded_secondAxis_decodes {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (hs : 0<s) (r : Fin a) (j : Fin B) :
    SameEdge (expandedVertex (by omega) hs (r,j,⟨s,by omega⟩),
      expandedVertex (by omega) hs (expandedNext (by omega) (by omega) (r,j,⟨s,by omega⟩)))
      (fineRepresentativeEdge hs (ownedEdge (by omega) (by omega) ⟨0,by decide⟩ false
        (if j.val=B-1 then successor (by omega) r else r) j)) := by
  have h := coordinate_step ha hB heven (r,j,(⟨1,by decide⟩ : Fin 2))
  have hh := map_sameEdge (representative hs) h
  have hsne : s≠0 := by omega
  by_cases hjnext : j.val+1<B
  · simpa [expandedVertex,expandedNext,coordinateNext,coordinateLabel,fineRepresentativeEdge,hjnext,hsne] using hh
  · simpa [expandedVertex,expandedNext,coordinateNext,coordinateLabel,fineRepresentativeEdge,hjnext,hsne] using hh

theorem expanded_covers_secondAxis {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (hs : 0<s) (r : Fin a) (j : Fin B) :
    ∃ p, SameEdge (expandedVertex (by omega) hs p,expandedVertex (by omega) hs (expandedNext (by omega) (by omega) p))
      (fineRepresentativeEdge hs (ownedEdge (by omega) (by omega) ⟨0,by decide⟩ false r j)) := by
  by_cases hj : j.val=B-1
  · refine ⟨(predecessor (show 0<a by omega) r,j,⟨s,by omega⟩),?_⟩
    have h := expanded_secondAxis_decodes ha hB heven hs (predecessor (show 0<a by omega) r) j
    simpa only [hj,ite_true,successor_predecessor] using h
  · refine ⟨(r,j,⟨s,by omega⟩),?_⟩
    have h := expanded_secondAxis_decodes ha hB heven hs r j
    simpa only [hj,ite_false] using h

theorem fineRepresentativeEdge_translate {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (r : Fin a) (j : Fin B) :
    fineShiftEdge ha (fineRepresentativeEdge hs (ownedEdge ha hB ⟨0,by decide⟩ false r j))=
      fineRepresentativeEdge hs (ownedEdge ha hB ⟨1,by decide⟩ false (translatedBlock ha false r j) j) := by
  change fineRepresentativeEdge hs (shiftEdge ha (ownedEdge ha hB ⟨0,by decide⟩ false r j))=_
  rw [ownedEdge_translate]

theorem translated_covers_secondAxis {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (hs : 0<s) (r : Fin a) (j : Fin B) :
    ∃ p, SameEdge (translatedExpandedVertex (by omega) hs p,
      translatedExpandedVertex (by omega) hs (expandedNext (by omega) (by omega) p))
      (fineRepresentativeEdge hs (ownedEdge (by omega) (by omega) ⟨1,by decide⟩ false r j)) := by
  obtain ⟨r',hr⟩ := translatedBlock_surjective (show 0<a by omega) false j r
  change translatedBlock (show 0<a by omega) false r' j=r at hr
  obtain ⟨p,hp⟩ := expanded_covers_secondAxis ha hB heven hs r' j
  refine ⟨p,?_⟩
  have hh := map_sameEdge (fineShift (show 0<a by omega)) hp
  change SameEdge _ (fineShiftEdge _ _) at hh
  rw [fineRepresentativeEdge_translate,hr] at hh
  exact hh

def coordinateTour {a B s : Nat} (ha : 0<a) (hs : 0<s) (c : Bool)
    (p : Fin a × Fin B × Fin (s+1)) :=
  if c then translatedExpandedVertex ha hs p else expandedVertex ha hs p

def CoordinateCovered {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (e : FineVertex a B s × FineVertex a B s) : Prop :=
  ∃ c p, SameEdge (coordinateTour ha hs c p,coordinateTour ha hs c (expandedNext ha hB p)) e

theorem coordinateCovered_sameEdge {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    {e f : FineVertex a B s × FineVertex a B s} (he : CoordinateCovered ha hB hs e)
    (h : SameEdge e f) : CoordinateCovered ha hB hs f := by
  obtain ⟨c,p,hp⟩ := he
  exact ⟨c,p,sameEdge_trans hp h⟩

theorem coordinateCovered_first {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (u : Fin (2*a) × Fin B) (k : Fin s) : CoordinateCovered ha hB hs (fineIntervalEdge ha hs u k) := by
  obtain ⟨p,hp⟩ := origin_surjective true u
  change origin p.1 true p.2.1 p.2.2=u at hp
  have hc := p.1.isLt
  by_cases hc0 : p.1.val=0
  · have he : p.1=(⟨0,by decide⟩ : Fin 2) := Fin.ext hc0
    obtain ⟨q,hq⟩ := expanded_covers_firstAxis ha hB hs p.2.1 p.2.2 k
    rw [he] at hp
    rw [hp] at hq
    exact ⟨false,q,hq⟩
  · have hcv : p.1.val=1 := by omega
    have he : p.1=(⟨1,by decide⟩ : Fin 2) := Fin.ext hcv
    obtain ⟨q,hq⟩ := translated_covers_firstAxis ha hB hs p.2.1 p.2.2 k
    rw [he] at hp
    rw [hp] at hq
    exact ⟨true,q,hq⟩

theorem coordinateCovered_second {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (hs : 0<s) (u : Fin (2*a) × Fin B) :
    CoordinateCovered (show 0<a by omega) (show 0<B by omega) hs
      (fineRepresentativeEdge hs (axisEdge (by omega) (by omega) false u)) := by
  obtain ⟨p,hp⟩ := origin_surjective false u
  change origin p.1 false p.2.1 p.2.2=u at hp
  have hc := p.1.isLt
  by_cases hc0 : p.1.val=0
  · have he : p.1=(⟨0,by decide⟩ : Fin 2) := Fin.ext hc0
    obtain ⟨q,hq⟩ := expanded_covers_secondAxis ha hB heven hs p.2.1 p.2.2
    rw [he] at hp
    unfold ownedEdge at hq
    rw [hp] at hq
    exact ⟨false,q,hq⟩
  · have hcv : p.1.val=1 := by omega
    have he : p.1=(⟨1,by decide⟩ : Fin 2) := Fin.ext hcv
    obtain ⟨q,hq⟩ := translated_covers_secondAxis ha hB heven hs p.2.1 p.2.2
    rw [he] at hp
    unfold ownedEdge at hq
    rw [hp] at hq
    exact ⟨true,q,hq⟩

theorem coordinatePair_cover {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (hs : 0<s) (u v : FineVertex a B s)
    (h : FineAdjacent (show 0<a by omega) (show 0<B by omega) hs u v) :
    CoordinateCovered (show 0<a by omega) (show 0<B by omega) hs (u,v) := by
  rcases h with h | h | ⟨hu,hv,hx,hy|hy⟩
  · have hh := coordinateCovered_first (show 0<a by omega) (show 0<B by omega) hs u.1 u.2
    change CoordinateCovered _ _ _ (u,fineNext _ _ u) at hh
    simpa only [h] using hh
  · have hh := coordinateCovered_first (show 0<a by omega) (show 0<B by omega) hs v.1 v.2
    change CoordinateCovered _ _ _ (v,fineNext _ _ v) at hh
    rw [h] at hh
    exact coordinateCovered_sameEdge _ _ _ hh (Or.inr rfl)
  · have ue : u=representative hs u.1 := Prod.ext rfl (Fin.ext hu)
    have ve : v=representative hs v.1 := Prod.ext rfl (Fin.ext hv)
    have hh := coordinateCovered_second ha hB heven hs u.1
    have he : fineRepresentativeEdge hs (axisEdge (show 0<2*a by omega) (show 0<B by omega) false u.1)=(u,v) := by
      apply Prod.ext
      · exact ue.symm
      · change representative hs (u.1.1,successor _ u.1.2)=v
        rw [hx,hy]
        exact ve.symm
    rw [he] at hh
    exact hh
  · have ue : u=representative hs u.1 := Prod.ext rfl (Fin.ext hu)
    have ve : v=representative hs v.1 := Prod.ext rfl (Fin.ext hv)
    have hh := coordinateCovered_second ha hB heven hs v.1
    have he : fineRepresentativeEdge hs (axisEdge (show 0<2*a by omega) (show 0<B by omega) false v.1)=(v,u) := by
      apply Prod.ext
      · exact ve.symm
      · change representative hs (v.1.1,successor _ v.1.2)=u
        rw [←hx,hy]
        exact ue.symm
    rw [he] at hh
    exact coordinateCovered_sameEdge _ _ _ hh (Or.inr rfl)

theorem expanded_nonzero_exclusive {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (p q : Fin a × Fin B × Fin (s+1)) (hp : (expandedVertex ha hs p).2.val≠0) :
    translatedExpandedVertex ha hs q≠expandedVertex ha hs p := by
  have h := interior_exclusive_zero ha hs p.1 p.2.1 (expandedVertex ha hs p).2 hp q
  have he : expandedVertex ha hs p=(origin (⟨0,by decide⟩ : Fin 2) true p.1 p.2.1,
      (expandedVertex ha hs p).2) := Prod.ext (expanded_internal_source ha hs p hp) rfl
  rw [he]
  exact h

theorem translated_nonzero_exclusive {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (p q : Fin a × Fin B × Fin (s+1)) (hp : (translatedExpandedVertex ha hs p).2.val≠0) :
    expandedVertex ha hs q≠translatedExpandedVertex ha hs p := by
  have h := interior_exclusive_one ha hs (translatedBlock ha true p.1 p.2.1) p.2.1
    (translatedExpandedVertex ha hs p).2 hp q
  have he : translatedExpandedVertex ha hs p=
      (origin (⟨1,by decide⟩ : Fin 2) true (translatedBlock ha true p.1 p.2.1) p.2.1,
       (translatedExpandedVertex ha hs p).2) := Prod.ext (translated_internal_source ha hs p hp) rfl
  rw [he]
  exact h

set_option linter.unusedSimpArgs false in
theorem firstAxis_has_interior {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 2≤s)
    (p : Fin a × Fin B × Fin (s+1)) (hp : p.2.2.val<s) :
    (expandedVertex ha (by omega) p).2.val≠0 ∨
    (expandedVertex ha (by omega) (expandedNext ha hB p)).2.val≠0 := by
  by_cases hp0 : p.2.2.val=0
  · apply Or.inr
    have hk0 : (⟨p.2.2.val+1,by omega⟩ : Fin (s+1)).val≠0 := by change p.2.2.val+1≠0; omega
    have hkS : (⟨p.2.2.val+1,by omega⟩ : Fin (s+1)).val≠s := by change p.2.2.val+1≠s; omega
    have hn := interiorOffset_positive p.2.1 ⟨p.2.2.val+1,by omega⟩ hk0 hkS
    simp [expandedNext,hp,expandedVertex,hk0,hkS]
    omega
  · apply Or.inl
    have hpS : p.2.2.val≠s := by omega
    have hn := interiorOffset_positive p.2.1 p.2.2 hp0 hpS
    simp [expandedVertex,hp0,hpS]
    omega

theorem translated_secondAxis_decodes {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (hs : 0<s) (r : Fin a) (j : Fin B) :
    SameEdge (translatedExpandedVertex (by omega) hs (r,j,⟨s,by omega⟩),
      translatedExpandedVertex (by omega) hs (expandedNext (by omega) (by omega) (r,j,⟨s,by omega⟩)))
      (fineRepresentativeEdge hs (ownedEdge (by omega) (by omega) ⟨1,by decide⟩ false
        (translatedBlock (by omega) false (if j.val=B-1 then successor (by omega) r else r) j) j)) := by
  have hh := map_sameEdge (fineShift (show 0<a by omega)) (expanded_secondAxis_decodes ha hB heven hs r j)
  change SameEdge _ (fineShiftEdge _ _) at hh
  rw [fineRepresentativeEdge_translate] at hh
  exact hh

theorem coordinatePair_disjoint {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (hs : 2≤s) (p q : Fin a × Fin B × Fin (s+1)) :
    ¬SameEdge (expandedVertex (by omega) (by omega) p,
      expandedVertex (by omega) (by omega) (expandedNext (by omega) (by omega) p))
      (translatedExpandedVertex (by omega) (by omega) q,
       translatedExpandedVertex (by omega) (by omega) (expandedNext (by omega) (by omega) q)) := by
  intro h
  by_cases hp : p.2.2.val<s
  · rcases firstAxis_has_interior (show 0<a by omega) (show 0<B by omega) hs p hp with hp | hp
    · rcases h with h | h
      · exact expanded_nonzero_exclusive _ _ p q hp (congrArg Prod.fst h).symm
      · exact expanded_nonzero_exclusive _ _ p (expandedNext _ _ q) hp (congrArg Prod.fst h).symm
    · rcases h with h | h
      · exact expanded_nonzero_exclusive _ _ (expandedNext _ _ p) (expandedNext _ _ q) hp (congrArg Prod.snd h).symm
      · exact expanded_nonzero_exclusive _ _ (expandedNext _ _ p) q hp (congrArg Prod.snd h).symm
  · by_cases hq : q.2.2.val<s
    · rcases firstAxis_has_interior (show 0<a by omega) (show 0<B by omega) hs q hq with hq | hq
      · have ht : (translatedExpandedVertex (show 0<a by omega) (show 0<s by omega) q).2.val≠0 := hq
        rcases h with h | h
        · exact translated_nonzero_exclusive _ _ q p ht (congrArg Prod.fst h)
        · exact translated_nonzero_exclusive _ _ q (expandedNext _ _ p) ht (congrArg Prod.snd h)
      · have ht : (translatedExpandedVertex (show 0<a by omega) (show 0<s by omega) (expandedNext _ _ q)).2.val≠0 := hq
        rcases h with h | h
        · exact translated_nonzero_exclusive _ _ (expandedNext _ _ q) (expandedNext _ _ p) ht (congrArg Prod.snd h)
        · exact translated_nonzero_exclusive _ _ (expandedNext _ _ q) p ht (congrArg Prod.fst h)
    · have hpend : p.2.2.val=s := by have := p.2.2.isLt; omega
      have hqend : q.2.2.val=s := by have := q.2.2.isLt; omega
      have hpf : p.2.2=(⟨s,by omega⟩ : Fin (s+1)) := Fin.ext hpend
      have hqf : q.2.2=(⟨s,by omega⟩ : Fin (s+1)) := Fin.ext hqend
      have h0 := expanded_secondAxis_decodes ha hB heven (show 0<s by omega) p.1 p.2.1
      have h1 := translated_secondAxis_decodes ha hB heven (show 0<s by omega) q.1 q.2.1
      simp only [←hpf] at h0
      simp only [←hqf] at h1
      have he := sameEdge_trans (sameEdge_symm h0) (sameEdge_trans h h1)
      have hc := map_sameEdge (fun z : FineVertex a B s => z.1) he
      simp only [fineRepresentativeEdge,representative] at hc
      have hc' : SameEdge
        (ownedEdge (show 0<a by omega) (show 0<B by omega) ⟨0,by decide⟩ false
          (if p.2.1.val=B-1 then successor (by omega) p.1 else p.1) p.2.1)
        (ownedEdge (show 0<a by omega) (show 0<B by omega) ⟨1,by decide⟩ false
          (translatedBlock (by omega) false (if q.2.1.val=B-1 then successor (by omega) q.1 else q.1) q.2.1) q.2.1) := hc
      have hu := ownedEdge_unique ha (show 3≤B by omega) _ _ _ _ _ _ _ _ hc'
      have hb := congrArg Fin.val hu.1
      change (0:Nat)=1 at hb
      omega

/-- Complete actual equal-length two-cycle partition of the uniformly
first-axis subdivided even torus. Tours share representatives and have
exclusive interior vertices; surjectivity of an individual tour is not assumed. -/
theorem subdividedTorusCycleDecomposition {a B s : Nat} (ha : 2≤a) (hB : 4≤B)
    (heven : B%2=0) (hs : 2≤s) :
    ∃ tour : Bool → Fin (a*(B*(s+1))) → FineVertex a B s,
      (∀ c, Function.Injective (tour c)) ∧
      (∀ c t, FineAdjacent (show 0<a by omega) (show 0<B by omega) (show 0<s by omega)
        (tour c t) (tour c (successor (Nat.mul_pos (show 0<a by omega)
          (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) t))) ∧
      (∀ u v, FineAdjacent (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) u v →
        ∃ c t, SameEdge (tour c t,tour c (successor (Nat.mul_pos (show 0<a by omega)
          (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) t)) (u,v)) ∧
      (∀ c d t w, SameEdge
        (tour c t,tour c (successor (Nat.mul_pos (show 0<a by omega)
          (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) t))
        (tour d w,tour d (successor (Nat.mul_pos (show 0<a by omega)
          (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) w)) → c=d ∧ t=w) := by
  let tour : Bool → Fin (a*(B*(s+1))) → FineVertex a B s :=
    fun c => if c then translatedExpandedCycle (show 0<a by omega) (show 0<B by omega) (show 0<s by omega)
      else expandedCycle (show 0<a by omega) (show 0<B by omega) (show 0<s by omega)
  have hinj : ∀ c, Function.Injective (tour c) := by
    intro c; cases c
    · exact expandedCycle_injective _ _ _
    · exact translatedExpandedCycle_injective _ _ _
  have hsize : 3≤a*(B*(s+1)) := by
    have hm : 2*(4*3)≤a*(B*(s+1)) := Nat.mul_le_mul ha (Nat.mul_le_mul hB (by omega))
    omega
  have hdis (t w : Fin (a*(B*(s+1)))) :
      ¬SameEdge (tour false t,tour false (successor (Nat.mul_pos (show 0<a by omega)
        (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) t))
        (tour true w,tour true (successor (Nat.mul_pos (show 0<a by omega)
        (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) w)) := by
    have hh := coordinatePair_disjoint ha hB heven hs
      (expandedCoordinates (show 0<B by omega) t) (expandedCoordinates (show 0<B by omega) w)
    simpa only [tour,Bool.false_eq_true,ite_false,ite_true,expandedCycle,translatedExpandedCycle,
      expandedCoordinates_next (show 0<a by omega) (show 0<B by omega) t,
      expandedCoordinates_next (show 0<a by omega) (show 0<B by omega) w] using hh
  refine ⟨tour,hinj,?_,?_,?_⟩
  · intro c t; cases c
    · exact expandedCycle_adjacent ha hB heven (by omega) t
    · exact translatedExpandedCycle_adjacent ha hB heven (by omega) t
  · intro u v huv
    obtain ⟨c,p,hp⟩ := coordinatePair_cover ha hB heven (show 0<s by omega) u v huv
    refine ⟨c,expandedIndex p,?_⟩
    have hcoord (c : Bool) (t : Fin (a*(B*(s+1)))) :
        tour c t=coordinateTour (show 0<a by omega) (show 0<s by omega) c
          (expandedCoordinates (show 0<B by omega) t) := by cases c <;> rfl
    rw [hcoord,hcoord,expandedCoordinates_next,expandedIndex_inverse]
    exact hp
  · intro c d t w h
    cases c <;> cases d
    · exact ⟨rfl,simpleCycle_step_unique hsize _ (hinj false) t w h⟩
    · exact False.elim (hdis t w h)
    · exact False.elim (hdis w t (sameEdge_symm h))
    · exact ⟨rfl,simpleCycle_step_unique hsize _ (hinj true) t w h⟩

#print axioms subdividedTorusCycleDecomposition
#print axioms coordinatePair_disjoint
#print axioms coordinatePair_cover
#print axioms expanded_covers_secondAxis
#print axioms translated_covers_firstAxis
#print axioms translated_covers_secondAxis
#print axioms expanded_covers_firstAxis
#print axioms subdividedCycle_equal_lengths
#print axioms translatedExpandedCycle_adjacent
#print axioms expandedCycle_adjacent
#print axioms expandedVertex_adjacent
#print axioms expandedVertex_firstAxis_step
#print axioms anchor_occurs_zero
#print axioms anchor_occurs_one
#print axioms rightNeighbor_exclusive
#print axioms leftNeighbor_exclusive
#print axioms rightNeighbor_occurs
#print axioms leftNeighbor_occurs
#print axioms rightNeighbor_adjacent
#print axioms leftNeighbor_adjacent
#print axioms interior_exclusive_zero
#print axioms interior_exclusive_one
#print axioms expandedCycle_injective
#print axioms translatedExpandedCycle_injective
#print axioms expandedCycle_list_nodup
#print axioms expandedVertex_injective
end ErdePaths.SubdividedWiggle
