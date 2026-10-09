import ErdePaths.SquareLift

namespace ErdePaths.Wiggle
open SquareLift

/-- Pair-coordinate encoding into the actual cyclic first coordinate. -/
def pairEncode {a : Nat} (p : Fin a × Fin 2) : Fin (2*a) :=
  ⟨2*p.1.val+p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩

theorem pairEncode_injective {a : Nat} : Function.Injective (@pairEncode a) := by
  intro p q h
  have he := congrArg Fin.val h
  have hp := p.2.isLt; have hq := q.2.isLt
  apply Prod.ext <;> apply Fin.ext <;> simp only [pairEncode] at he <;> omega

theorem pairEncode_surjective {a : Nat} : Function.Surjective (@pairEncode a) := by
  intro x
  refine ⟨(⟨x.val/2, by have := x.isLt; omega⟩,
    ⟨x.val%2, by omega⟩), ?_⟩
  apply Fin.ext
  simp only [pairEncode]
  omega

/-- The serpentine permutation in each ordinary row. -/
def rowParity (j : Nat) (b : Fin 2) : Fin 2 :=
  if j % 2 = 0 then b else b.rev

theorem rowParity_involutive (j : Nat) (b : Fin 2) :
    rowParity j (rowParity j b) = b := by
  simp only [rowParity]
  split <;> simp_all

theorem rowParity_injective (j : Nat) : Function.Injective (rowParity j) := by
  intro b c h
  have := congrArg (rowParity j) h
  simpa only [rowParity_involutive] using this

/-- The AOT two-wiggle traversal in a fixed row. Its last row shifts the
pair-coordinate encoding by one, producing the staircase to the next pair. -/
def rowMap {a B : Nat} (ha : 0 < a) (p : Fin a × Fin 2) (j : Fin B) : Fin (2*a) :=
  if j.val = B-1 then successor (by omega) (pairEncode p)
  else pairEncode (p.1,rowParity j.val p.2)

theorem rowMap_injective {a B : Nat} (ha : 0 < a) (j : Fin B) :
    Function.Injective (fun p => rowMap ha p j) := by
  intro p q h
  unfold rowMap at h
  split at h
  · have he := congrArg (predecessor (show 0 < 2*a by omega)) h
    simp only [predecessor_successor] at he
    exact pairEncode_injective he
  · have he := pairEncode_injective h
    have h1 := congrArg (fun z : Fin a × Fin 2 => z.1) he
    have h2 : rowParity j.val p.2 = rowParity j.val q.2 := congrArg (fun z : Fin a × Fin 2 => z.2) he
    exact Prod.ext h1 (rowParity_injective j.val h2)

theorem rowMap_surjective {a B : Nat} (ha : 0 < a) (j : Fin B) :
    Function.Surjective (fun p => rowMap ha p j) := by
  intro x
  by_cases hj : j.val = B-1
  · obtain ⟨p,hp⟩ := pairEncode_surjective (predecessor (show 0 < 2*a by omega) x)
    refine ⟨p,?_⟩
    simp [rowMap,hj,hp,successor_predecessor]
  · obtain ⟨p,hp⟩ := pairEncode_surjective x
    refine ⟨(p.1,rowParity j.val p.2),?_⟩
    simp [rowMap,hj,rowParity_involutive,hp]

/-- Explicit two-wiggle vertex order, indexed by block, row, and position
within the row. Consecutive lexicographic positions form the cycle. -/
def vertex {a B : Nat} (ha : 0 < a) (t : Fin a × Fin B × Fin 2) :
    Fin (2*a) × Fin B := (rowMap ha (t.1,t.2.2) t.2.1,t.2.1)

theorem vertex_injective {a B : Nat} (ha : 0 < a) :
    Function.Injective (@vertex a B ha) := by
  intro p q h
  have hj := congrArg Prod.snd h
  have hp := congrArg Prod.fst h
  simp only [vertex] at hj hp
  rw [hj] at hp
  have he := rowMap_injective ha q.2.1 hp
  have h1 := congrArg (fun z : Fin a × Fin 2 => z.1) he
  have h2 : p.2.2 = q.2.2 := congrArg (fun z : Fin a × Fin 2 => z.2) he
  exact Prod.ext h1 (Prod.ext hj h2)

theorem vertex_surjective {a B : Nat} (ha : 0 < a) :
    Function.Surjective (@vertex a B ha) := by
  intro x
  obtain ⟨p,hp⟩ := rowMap_surjective ha x.2 x.1
  exact ⟨(p.1,x.2,p.2),Prod.ext hp rfl⟩

/-- The second wiggle is the first-coordinate translation by one. -/
def translatedVertex {a B : Nat} (ha : 0 < a) (t : Fin a × Fin B × Fin 2) :
    Fin (2*a) × Fin B :=
  (successor (by omega) (vertex ha t).1,(vertex ha t).2)

theorem translatedVertex_injective {a B : Nat} (ha : 0 < a) :
    Function.Injective (@translatedVertex a B ha) := by
  intro p q h
  apply vertex_injective ha
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hh := congrArg (predecessor (show 0 < 2*a by omega)) hx
  simp only [translatedVertex,predecessor_successor] at hh hy
  exact Prod.ext hh hy

theorem translatedVertex_surjective {a B : Nat} (ha : 0 < a) :
    Function.Surjective (@translatedVertex a B ha) := by
  intro x
  obtain ⟨t,ht⟩ := vertex_surjective ha
    (predecessor (show 0 < 2*a by omega) x.1,x.2)
  refine ⟨t,?_⟩
  simp only [translatedVertex,ht,successor_predecessor]

/-- Mixed-radix index into the block/row/within-row coordinates. -/
def indexCoordinates {a B : Nat} (hB : 0 < B) (t : Fin (a*(B*2))) :
    Fin a × Fin B × Fin 2 :=
  (⟨t.val/(B*2), Nat.div_lt_of_lt_mul (by
    simpa only [Nat.mul_comm] using t.isLt)⟩,
   ⟨(t.val%(B*2))/2, by have := Nat.mod_lt t.val (show 0 < B*2 by omega); omega⟩,
   ⟨t.val%2, by omega⟩)

theorem indexCoordinates_reconstruct {a B : Nat} (hB : 0 < B)
    (t : Fin (a*(B*2))) :
    (indexCoordinates hB t).1.val*(B*2)+
    (indexCoordinates hB t).2.1.val*2+(indexCoordinates hB t).2.2.val = t.val := by
  have hm : (t.val%(B*2))%2=t.val%2 := Nat.mod_mod_of_dvd t.val (by omega : 2 ∣ B*2)
  have h1 := Nat.div_add_mod t.val (B*2)
  have h2 := Nat.div_add_mod (t.val%(B*2)) 2
  simp only [indexCoordinates]
  rw [Nat.mul_comm (B*2)] at h1
  omega

theorem indexCoordinates_injective {a B : Nat} (hB : 0 < B) :
    Function.Injective (@indexCoordinates a B hB) := by
  intro s t h
  have hs := indexCoordinates_reconstruct hB s
  have ht := indexCoordinates_reconstruct hB t
  rw [h] at hs
  apply Fin.ext
  omega

theorem indexCoordinates_surjective {a B : Nat} (hB : 0 < B) :
    Function.Surjective (@indexCoordinates a B hB) := by
  intro p
  have hi : p.2.1.val*2+p.2.2.val < B*2 := by
    have := p.2.1.isLt; have := p.2.2.isLt; omega
  have hb : (B*2)*p.1.val+(p.2.1.val*2+p.2.2.val) < a*(B*2) := by
    have hr := Nat.mul_le_mul_right (B*2) (show p.1.val+1 ≤ a by have := p.1.isLt; omega)
    rw [Nat.add_mul] at hr
    rw [Nat.mul_comm (B*2) p.1.val]
    omega
  refine ⟨⟨(B*2)*p.1.val+(p.2.1.val*2+p.2.2.val),hb⟩,?_⟩
  apply Prod.ext
  · apply Fin.ext
    simp only [indexCoordinates,Nat.mul_add_div (show B*2>0 by omega)]
    rw [Nat.div_eq_of_lt hi]
    omega
  · apply Prod.ext <;> apply Fin.ext
    · simp only [indexCoordinates,Nat.mul_add_mod,Nat.mod_eq_of_lt hi]
      have hp := p.2.2.isLt
      omega
    · simp only [indexCoordinates]
      have hm : ((B*2)*p.1.val+(p.2.1.val*2+p.2.2.val))%2 =
          (p.2.1.val*2+p.2.2.val)%2 := by
        have he : (B*2)*p.1.val=2*(B*p.1.val) := by rw [Nat.mul_comm B 2,Nat.mul_assoc]
        rw [he,Nat.mul_add_mod]
      rw [hm]
      have hp := p.2.2.isLt
      omega

/-- Closed cyclic vertex map with exactly (2a)B positions. -/
def cycle {a B : Nat} (ha : 0 < a) (hB : 0 < B)
    (t : Fin (a*(B*2))) : Fin (2*a) × Fin B := vertex ha (indexCoordinates hB t)

theorem cycle_injective {a B : Nat} (ha : 0 < a) (hB : 0 < B) :
    Function.Injective (@cycle a B ha hB) := by
  intro s t h
  exact indexCoordinates_injective hB (vertex_injective ha h)

theorem cycle_surjective {a B : Nat} (ha : 0 < a) (hB : 0 < B) :
    Function.Surjective (@cycle a B ha hB) := by
  intro x
  obtain ⟨p,hp⟩ := vertex_surjective ha x
  obtain ⟨t,ht⟩ := indexCoordinates_surjective hB p
  exact ⟨t,by simpa only [cycle,ht] using hp⟩

/-- Second closed candidate cycle: translate the first by one column. -/
def translatedCycle {a B : Nat} (ha : 0 < a) (hB : 0 < B)
    (t : Fin (a*(B*2))) : Fin (2*a) × Fin B :=
  translatedVertex ha (indexCoordinates hB t)

theorem translatedCycle_injective {a B : Nat} (ha : 0 < a) (hB : 0 < B) :
    Function.Injective (@translatedCycle a B ha hB) := by
  intro s t h
  exact indexCoordinates_injective hB (translatedVertex_injective ha h)

theorem translatedCycle_surjective {a B : Nat} (ha : 0 < a) (hB : 0 < B) :
    Function.Surjective (@translatedCycle a B ha hB) := by
  intro x
  obtain ⟨p,hp⟩ := translatedVertex_surjective ha x
  obtain ⟨t,ht⟩ := indexCoordinates_surjective hB p
  exact ⟨t,by simpa only [translatedCycle,ht] using hp⟩

/-- Actual rectangular torus adjacency, with either orientation accepted. -/
def TorusAdjacent {A B : Nat} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin A × Fin B) : Prop :=
  (u.2=v.2 ∧ (successor hA u.1=v.1 ∨ successor hA v.1=u.1)) ∨
  (u.1=v.1 ∧ (successor hB u.2=v.2 ∨ successor hB v.2=u.2))

/-- An actual clockwise rectangular torus edge. True means first axis. -/
def axisEdge {A B : Nat} (hA : 0 < A) (hB : 0 < B)
    (axis : Bool) (u : Fin A × Fin B) :
    (Fin A × Fin B) × (Fin A × Fin B) :=
  if axis then (u,(successor hA u.1,u.2)) else (u,(u.1,successor hB u.2))

theorem cyclic_arc_unique {N : Nat} (hN : 3 ≤ N) (i j : Fin N)
    (h : SameEdge (i,successor (by omega) i) (j,successor (by omega) j)) : i=j := by
  rcases h with h | h
  · exact congrArg Prod.fst h
  · have hi : i=successor (by omega) j := congrArg Prod.fst h
    have hj : successor (by omega) i=j := congrArg Prod.snd h
    have hn := successor_twice_ne (by omega) hN j
    rw [hi] at hj
    exact False.elim (hn hj)

theorem axisEdge_unique {A B : Nat} (hA : 3 ≤ A) (hB : 3 ≤ B)
    (axis axis' : Bool) (u v : Fin A × Fin B)
    (h : SameEdge (axisEdge (by omega) (by omega) axis u)
      (axisEdge (by omega) (by omega) axis' v)) : axis=axis' ∧ u=v := by
  cases axis <;> cases axis'
  · refine ⟨rfl,Prod.ext ?_ ?_⟩
    · rcases h with h | h <;> exact congrArg (fun e => e.1.1) h
    · apply cyclic_arc_unique hB
      rcases h with h | h
      · exact Or.inl (congrArg (fun e => (e.1.2,e.2.2)) h)
      · exact Or.inr (congrArg (fun e => (e.1.2,e.2.2)) h)
  · exfalso
    have hn := successor_ne (show 0 < A by omega) (show 2 ≤ A by omega) v.1
    rcases h with h | h
    · have h1 := congrArg (fun e => e.1.1) h
      have h2 := congrArg (fun e => e.2.1) h
      simp only [axisEdge,Bool.false_eq_true,ite_false,ite_true] at h1 h2
      exact hn (h2.symm.trans h1)
    · have h1 := congrArg (fun e => e.1.1) h
      have h2 := congrArg (fun e => e.2.1) h
      simp only [axisEdge,Bool.false_eq_true,ite_false,ite_true] at h1 h2
      exact hn (h1.symm.trans h2)
  · exfalso
    have hn := successor_ne (show 0 < A by omega) (show 2 ≤ A by omega) u.1
    rcases h with h | h
    · have h1 := congrArg (fun e => e.1.1) h
      have h2 := congrArg (fun e => e.2.1) h
      simp only [axisEdge,Bool.false_eq_true,ite_false,ite_true] at h1 h2
      exact hn (h2.trans h1.symm)
    · have h1 := congrArg (fun e => e.1.1) h
      have h2 := congrArg (fun e => e.2.1) h
      simp only [axisEdge,Bool.false_eq_true,ite_false,ite_true] at h1 h2
      exact hn (h2.trans h1.symm)
  · refine ⟨rfl,Prod.ext ?_ ?_⟩
    · apply cyclic_arc_unique hA
      rcases h with h | h
      · exact Or.inl (congrArg (fun e => (e.1.1,e.2.1)) h)
      · exact Or.inr (congrArg (fun e => (e.1.1,e.2.1)) h)
    · rcases h with h | h <;> exact congrArg (fun e => e.1.2) h

/-- AOT k=2 edge-color formulas: first-axis seam flips color;
second-axis color is first-coordinate parity plus row plus one. -/
def origin {a B : Nat} (color : Fin 2) (axis : Bool) (r : Fin a) (j : Fin B) :
    Fin (2*a) × Fin B :=
  (pairEncode (r,if axis then
    (if j.val=B-1 then color.rev else color)
    else rowParity (j.val+1) color),j)

/-- Color/axis/block/row labels decode actual edges, rather than abstract slots. -/
def ownedEdge {a B : Nat} (ha : 0 < a) (hB : 0 < B)
    (color : Fin 2) (axis : Bool) (r : Fin a) (j : Fin B) :=
  axisEdge (show 0 < 2*a by omega) hB axis (origin color axis r j)

theorem ownedEdge_adjacent {a B : Nat} (ha : 0 < a) (hB : 0 < B)
    (c : Fin 2) (axis : Bool) (r : Fin a) (j : Fin B) :
    TorusAdjacent (show 0 < 2*a by omega) hB
      (ownedEdge ha hB c axis r j).1 (ownedEdge ha hB c axis r j).2 := by
  cases axis
  · exact Or.inr ⟨rfl,Or.inl rfl⟩
  · exact Or.inl ⟨rfl,Or.inl rfl⟩

 theorem origin_injective {a B : Nat} (axis : Bool) :
    Function.Injective (fun p : Fin 2 × Fin a × Fin B => origin p.1 axis p.2.1 p.2.2) := by
  intro p q h
  have hj := congrArg Prod.snd h
  have hx := congrArg Prod.fst h
  simp only [origin] at hj hx
  rw [hj] at hx
  have he := pairEncode_injective hx
  have hr := congrArg Prod.fst he
  have hc := congrArg Prod.snd he
  have hcol : p.1=q.1 := by
    cases axis
    · exact rowParity_injective (q.2.2.val+1) hc
    · simp only [ite_true] at hc
      split at hc
      · exact Fin.rev_inj.mp hc
      · exact hc
  exact Prod.ext hcol (Prod.ext hr hj)

 theorem origin_surjective {a B : Nat} (axis : Bool) :
    Function.Surjective (fun p : Fin 2 × Fin a × Fin B => origin p.1 axis p.2.1 p.2.2) := by
  intro x
  obtain ⟨p,hp⟩ := pairEncode_surjective x.1
  cases axis
  · refine ⟨(rowParity (x.2.val+1) p.2,p.1,x.2),?_⟩
    simp [origin,rowParity_involutive,hp]
  · by_cases hj : x.2.val=B-1
    · refine ⟨(p.2.rev,p.1,x.2),?_⟩
      simp [origin,hj,hp]
    · refine ⟨(p.2,p.1,x.2),?_⟩
      simp [origin,hj,hp]

 theorem ownedEdge_unique {a B : Nat} (ha : 2 ≤ a) (hB : 3 ≤ B)
    (c d : Fin 2) (axis axis' : Bool) (r s : Fin a) (j k : Fin B)
    (h : SameEdge (ownedEdge (by omega) (by omega) c axis r j)
      (ownedEdge (by omega) (by omega) d axis' s k)) :
    c=d ∧ axis=axis' ∧ r=s ∧ j=k := by
  have he := axisEdge_unique (show 3 ≤ 2*a by omega) hB axis axis'
    (origin c axis r j) (origin d axis' s k) h
  have hx := he.2
  rw [←he.1] at hx
  have hi : (c,r,j)=(d,s,k) := origin_injective axis hx
  exact ⟨congrArg Prod.fst hi,he.1,
    congrArg (fun p => p.2.1) hi,congrArg (fun p => p.2.2) hi⟩

 theorem ownedEdge_cover {a B : Nat} (ha : 0 < a) (hB : 0 < B)
    (u v : Fin (2*a) × Fin B) (h : TorusAdjacent (by omega) hB u v) :
    ∃ c axis r j, SameEdge (ownedEdge ha hB c axis r j) (u,v) := by
  rcases h with ⟨hy,hx|hx⟩ | ⟨hx,hy|hy⟩
  · obtain ⟨p,hp⟩ := origin_surjective true u
    refine ⟨p.1,true,p.2.1,p.2.2,Or.inl ?_⟩
    simp only [ownedEdge,axisEdge,hp,ite_true]
    exact Prod.ext rfl (Prod.ext hx hy)
  · obtain ⟨p,hp⟩ := origin_surjective true v
    refine ⟨p.1,true,p.2.1,p.2.2,Or.inr ?_⟩
    simp only [ownedEdge,axisEdge,hp,ite_true]
    exact Prod.ext rfl (Prod.ext hx hy.symm)
  · obtain ⟨p,hp⟩ := origin_surjective false u
    refine ⟨p.1,false,p.2.1,p.2.2,Or.inl ?_⟩
    simp only [ownedEdge,axisEdge,hp,Bool.false_eq_true,ite_false]
    exact Prod.ext rfl (Prod.ext hx hy)
  · obtain ⟨p,hp⟩ := origin_surjective false v
    refine ⟨p.1,false,p.2.1,p.2.2,Or.inr ?_⟩
    simp only [ownedEdge,axisEdge,hp,Bool.false_eq_true,ite_false]
    exact Prod.ext rfl (Prod.ext hx.symm hy)

/-- Uniform length/axis-balance enumeration; there are aB actual edges of
each color and each axis, with no duplicate edge positions. -/
def balancedEdge {a B : Nat} (ha : 0 < a) (hB : 0 < B)
    (c : Fin 2) (axis : Bool) (t : Fin (a*B)) :=
  ownedEdge ha hB c axis
    ⟨t.val/B,Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using t.isLt)⟩
    ⟨t.val%B,Nat.mod_lt _ hB⟩

theorem balancedEdge_injective {a B : Nat} (ha : 2 ≤ a) (hB : 3 ≤ B)
    (c : Fin 2) (axis : Bool) :
    Function.Injective (balancedEdge (show 0<a by omega) (show 0<B by omega) c axis) := by
  intro s t h
  have hu := ownedEdge_unique ha hB c c axis axis
    ⟨s.val/B,Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using s.isLt)⟩
    ⟨t.val/B,Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using t.isLt)⟩
    ⟨s.val%B,Nat.mod_lt _ (show 0<B by omega)⟩
    ⟨t.val%B,Nat.mod_lt _ (show 0<B by omega)⟩ (Or.inl h)
  have hq := congrArg Fin.val hu.2.2.1
  have hr := congrArg Fin.val hu.2.2.2
  change s.val/B=t.val/B at hq
  change s.val%B=t.val%B at hr
  have hs := Nat.div_add_mod s.val B
  have ht := Nat.div_add_mod t.val B
  rw [hq,hr] at hs
  apply Fin.ext
  omega

theorem balancedEdge_covers_labels {a B : Nat} (ha : 0 < a) (hB : 0 < B)
    (c : Fin 2) (axis : Bool) (r : Fin a) (j : Fin B) :
    ∃ t, balancedEdge ha hB c axis t=ownedEdge ha hB c axis r j := by
  have ht : B*r.val+j.val < a*B := by
    have hr := Nat.mul_le_mul_right B (show r.val+1 ≤ a by have := r.isLt; omega)
    rw [Nat.add_mul] at hr
    rw [Nat.mul_comm B r.val]
    have := j.isLt
    omega
  refine ⟨⟨B*r.val+j.val,ht⟩,?_⟩
  have hq : (B*r.val+j.val)/B=r.val := by
    rw [Nat.mul_add_div hB,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hm : (B*r.val+j.val)%B=j.val := by
    rw [Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  unfold balancedEdge
  simp only [hq,hm]

theorem balancedEdge_list_nodup {a B : Nat} (ha : 2 ≤ a) (hB : 3 ≤ B)
    (c : Fin 2) (axis : Bool) :
    (List.ofFn (balancedEdge (show 0<a by omega) (show 0<B by omega) c axis)).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  simp only [List.getElem_ofFn] at he
  exact congrArg Fin.val (balancedEdge_injective ha hB c axis he)

theorem balancedEdge_list_length {a B : Nat} (ha : 0 < a) (hB : 0 < B)
    (c : Fin 2) (axis : Bool) :
    (List.ofFn (balancedEdge ha hB c axis)).length=a*B := List.length_ofFn

/-- Each color's weighted edge count after uniformly subdividing the first
axis into s edges. This is an edge-count theorem, not a connectivity claim. -/
theorem uniform_subdivision_count (a B s : Nat) :
    a*B*s+a*B=(2*a)*B*(s+1)/2 := by
  have he : (2*a)*B*(s+1)=2*(a*B*(s+1)) := by simp only [Nat.mul_assoc]
  rw [he,Nat.mul_div_cancel_left _ (show 0<2 by decide)]
  simp only [Nat.mul_add,Nat.mul_one]

 theorem cycle_list_nodup {a B : Nat} (ha : 0 < a) (hB : 0 < B) :
    (List.ofFn (cycle ha hB)).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  simp only [List.getElem_ofFn] at he
  exact congrArg Fin.val (cycle_injective ha hB he)

 theorem cycle_list_length {a B : Nat} (ha : 0 < a) (hB : 0 < B) :
    (List.ofFn (cycle ha hB)).length=(2*a)*B := by
  simp only [List.length_ofFn]
  simp only [Nat.mul_comm,Nat.mul_left_comm]

/-- Forced lexicographic cyclic successor in the traversal coordinates. -/
def coordinateNext {a B : Nat} (ha : 0<a) (hB : 0<B)
    (t : Fin a × Fin B × Fin 2) : Fin a × Fin B × Fin 2 :=
  if t.2.2.val=0 then (t.1,t.2.1,⟨1,by decide⟩)
  else if hj : t.2.1.val+1<B then (t.1,⟨t.2.1.val+1,hj⟩,⟨0,by decide⟩)
  else (successor ha t.1,⟨0,hB⟩,⟨0,by decide⟩)

/-- Label of the actual colored edge traversed at a coordinate position. -/
def coordinateLabel {a B : Nat} (ha : 0<a) (t : Fin a × Fin B × Fin 2) :
    Bool × Fin a × Fin B :=
  (t.2.2.val=0,
   if t.2.2.val=0 ∨ t.2.1.val≠B-1 then t.1 else successor ha t.1,
   t.2.1)

set_option linter.unusedSimpArgs false in
 theorem coordinate_step {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (t : Fin a × Fin B × Fin 2) :
    SameEdge (vertex (by omega) t,
      vertex (by omega) (coordinateNext (by omega) (by omega) t))
      (ownedEdge (by omega) (by omega) ⟨0,by decide⟩
        (coordinateLabel (by omega) t).1
        (coordinateLabel (by omega) t).2.1
        (coordinateLabel (by omega) t).2.2) := by
  rcases t with ⟨r,j,b⟩
  have hr := r.isLt
  have hj := j.isLt
  have hb := b.isLt
  have hxmod : (2*r.val+1)%(2*a)=2*r.val+1 := Nat.mod_eq_of_lt (by omega)
  have hBpred : B-1+1=B := by omega
  have hxwrap : (2*r.val+1+1)%(2*a)=2*((r.val+1)%a) := by
    by_cases hrr : r.val+1<a
    · rw [Nat.mod_eq_of_lt (show 2*r.val+1+1<2*a by omega),Nat.mod_eq_of_lt hrr]
      omega
    · have he : r.val+1=a := by omega
      have he' : 2*r.val+1+1=2*a := by omega
      simp only [he,he',Nat.mod_self,Nat.mul_zero]
  by_cases hb0 : b.val=0
  · have hbfin : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb0
    subst b
    by_cases hjlast : j.val=B-1
    · apply Or.inl
      simp [vertex,rowMap,hjlast,coordinateNext,coordinateLabel,
        ownedEdge,axisEdge,origin,pairEncode,Fin.rev,Fin.ext_iff,successor,hxmod,hBpred,heven]
    · by_cases hjpar : j.val%2=0
      · apply Or.inl
        simp [vertex,rowMap,hjlast,coordinateNext,coordinateLabel,
          ownedEdge,axisEdge,origin,pairEncode,rowParity,hjpar,Fin.ext_iff,successor,hxmod,hBpred,heven]
      · apply Or.inr
        simp [vertex,rowMap,hjlast,coordinateNext,coordinateLabel,
          ownedEdge,axisEdge,origin,pairEncode,rowParity,hjpar,Fin.rev,Fin.ext_iff,successor,hxmod,hBpred,heven]
  · have hbval : b.val=1 := by omega
    have hbfin : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext hbval
    subst b
    apply Or.inl
    by_cases hjnext : j.val+1<B
    · have hjlast : j.val≠B-1 := by omega
      have hjmod : (j.val+1)%B=j.val+1 := Nat.mod_eq_of_lt hjnext
      by_cases hjnear : j.val+1=B-1
      · have hp : j.val%2=0 := by omega
        have hp' : (j.val+1)%2≠0 := by omega
        simp [vertex,rowMap,coordinateNext,coordinateLabel,ownedEdge,axisEdge,
          origin,pairEncode,rowParity,Fin.rev,hjnext,hjlast,hjnear,hp,hp',Fin.ext_iff,successor,hxmod,hBpred,heven,hjmod]
        simp_all [Nat.mod_eq_of_lt (show B-1<B by omega)]
      · by_cases hp : j.val%2=0
        · have hp' : (j.val+1)%2≠0 := by omega
          simp [vertex,rowMap,coordinateNext,coordinateLabel,ownedEdge,axisEdge,
            origin,pairEncode,rowParity,Fin.rev,hjnext,hjlast,hjnear,hp,hp',Fin.ext_iff,successor,hxmod,hBpred,heven,hjmod]
        · have hp' : (j.val+1)%2=0 := by omega
          simp [vertex,rowMap,coordinateNext,coordinateLabel,ownedEdge,axisEdge,
            origin,pairEncode,rowParity,Fin.rev,hjnext,hjlast,hjnear,hp,hp',Fin.ext_iff,successor,hxmod,hBpred,heven,hjmod]
    · have hjlast : j.val=B-1 := by omega
      have hp : (j.val+1)%2=0 := by omega
      have hz : (0:Nat)≠B-1 := by omega
      simp [vertex,rowMap,coordinateNext,coordinateLabel,ownedEdge,axisEdge,
        origin,pairEncode,rowParity,Fin.rev,hjnext,hjlast,hp,hz,Fin.ext_iff,successor,hxmod,hBpred,heven]
      simp_all [hxwrap]

theorem coordinateLabel_surjective {a B : Nat} (ha : 0<a) :
    Function.Surjective (@coordinateLabel a B ha) := by
  intro p
  rcases p with ⟨axis,r,j⟩
  cases axis
  · by_cases hj : j.val=B-1
    · refine ⟨(predecessor ha r,j,⟨1,by decide⟩),?_⟩
      simp [coordinateLabel,hj,successor_predecessor]
    · refine ⟨(r,j,⟨1,by decide⟩),?_⟩
      simp [coordinateLabel,hj]
  · refine ⟨(r,j,⟨0,by decide⟩),?_⟩
    simp [coordinateLabel]

theorem coordinateLabel_injective {a B : Nat} (ha : 0<a) :
    Function.Injective (@coordinateLabel a B ha) := by
  intro p q h
  rcases p with ⟨r,j,b⟩
  rcases q with ⟨s,k,c⟩
  have haxis := congrArg (fun z => z.1) h
  have hj := congrArg (fun z => z.2.2) h
  change j=k at hj
  subst k
  have hb := b.isLt; have hc := c.isLt
  by_cases hb0 : b.val=0 <;> by_cases hc0 : c.val=0
  · have hbfin : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb0
    have hcfin : c=(⟨0,by decide⟩ : Fin 2) := Fin.ext hc0
    subst b; subst c
    have hr := congrArg (fun z => z.2.1) h
    simp only [coordinateLabel] at hr
    simpa using congrArg (fun x => (x,j,(⟨0,by decide⟩ : Fin 2))) hr
  · simp [coordinateLabel,hb0,hc0] at haxis
  · simp [coordinateLabel,hb0,hc0] at haxis
  · have hbval : b.val=1 := by omega
    have hcval : c.val=1 := by omega
    have hbfin : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext hbval
    have hcfin : c=(⟨1,by decide⟩ : Fin 2) := Fin.ext hcval
    subst b; subst c
    have hr := congrArg (fun z => z.2.1) h
    by_cases hjlast : j.val=B-1
    · simp [coordinateLabel,hjlast] at hr
      have he := congrArg (predecessor ha) hr
      simp only [predecessor_successor] at he
      exact congrArg (fun x => (x,j,(⟨1,by decide⟩ : Fin 2))) he
    · simp [coordinateLabel,hjlast] at hr
      exact congrArg (fun x => (x,j,(⟨1,by decide⟩ : Fin 2))) hr

/-- Explicit scalar position of the lexicographic coordinate. -/
def coordinateIndex {a B : Nat} (_hB : 0<B) (p : Fin a × Fin B × Fin 2) :
    Fin (a*(B*2)) :=
  ⟨(B*2)*p.1.val+(p.2.1.val*2+p.2.2.val),by
    have hi : p.2.1.val*2+p.2.2.val<B*2 := by
      have := p.2.1.isLt; have := p.2.2.isLt; omega
    have hr := Nat.mul_le_mul_right (B*2) (show p.1.val+1 ≤ a by have := p.1.isLt; omega)
    rw [Nat.add_mul] at hr
    rw [Nat.mul_comm (B*2) p.1.val]
    omega⟩

theorem coordinateIndex_inverse {a B : Nat} (hB : 0<B) (p : Fin a × Fin B × Fin 2) :
    indexCoordinates hB (coordinateIndex hB p)=p := by
  obtain ⟨t,ht⟩ := indexCoordinates_surjective hB p
  have hn := indexCoordinates_reconstruct hB t
  rw [ht] at hn
  have hi : coordinateIndex hB p=t := by
    apply Fin.ext
    change (B*2)*p.1.val+(p.2.1.val*2+p.2.2.val)=t.val
    rw [Nat.mul_comm (B*2)]
    omega
  rw [hi]
  exact ht

theorem coordinateIndex_reverse {a B : Nat} (hB : 0<B) (t : Fin (a*(B*2))) :
    coordinateIndex hB (indexCoordinates hB t)=t := by
  apply indexCoordinates_injective hB
  exact coordinateIndex_inverse hB _

set_option linter.unusedSimpArgs false in
theorem coordinateIndex_next {a B : Nat} (ha : 0<a) (hB : 0<B)
    (p : Fin a × Fin B × Fin 2) :
    coordinateIndex hB (coordinateNext ha hB p)=
      successor (show 0<a*(B*2) by exact Nat.mul_pos ha (by omega)) (coordinateIndex hB p) := by
  rcases p with ⟨r,j,b⟩
  have hr := r.isLt; have hj := j.isLt; have hb := b.isLt
  have hn := (coordinateIndex hB (r,j,b)).isLt
  change (B*2)*r.val+(j.val*2+b.val)<a*(B*2) at hn
  by_cases hb0 : b.val=0
  · have hbfin : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb0
    subst b
    apply Fin.ext
    simp [coordinateIndex,coordinateNext,successor]
    apply Eq.symm
    apply Nat.mod_eq_of_lt
    have hbound := Nat.mul_le_mul_right (B*2) (show r.val+1≤a by omega)
    rw [Nat.add_mul,Nat.mul_comm r.val] at hbound
    omega
  · have hbval : b.val=1 := by omega
    have hbfin : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext hbval
    subst b
    by_cases hjnext : j.val+1<B
    · apply Fin.ext
      simp [coordinateIndex,coordinateNext,hjnext,successor]
      have hmod : ((B*2)*r.val+(j.val*2+1)+1)%(a*(B*2))=
          (B*2)*r.val+(j.val*2+1)+1 := Nat.mod_eq_of_lt (by
            have hbound := Nat.mul_le_mul_right (B*2) (show r.val+1≤a by omega)
            rw [Nat.add_mul,Nat.mul_comm r.val] at hbound
            omega)
      rw [hmod]
      omega
    · have hjlast : j.val=B-1 := by omega
      have hBpred : B-1+1=B := by omega
      by_cases hrnext : r.val+1<a
      · have hrmod : (r.val+1)%a=r.val+1 := Nat.mod_eq_of_lt hrnext
        apply Fin.ext
        simp [coordinateIndex,coordinateNext,hjnext,hjlast,hBpred,successor,hrmod]
        have hn' : (B*2)*r.val+((B-1)*2+1)+1<a*(B*2) := by
          have hbound := Nat.mul_lt_mul_of_pos_right hrnext (show 0<B*2 by omega)
          rw [Nat.add_mul,Nat.mul_comm r.val] at hbound
          omega
        rw [Nat.mod_eq_of_lt hn',Nat.mul_add]
        omega
      · have hrend : r.val+1=a := by omega
        have hrmod : (r.val+1)%a=0 := by simp [hrend]
        apply Fin.ext
        simp [coordinateIndex,coordinateNext,hjnext,hjlast,hBpred,successor,hrmod]
        have he : (B*2)*r.val+((B-1)*2+1)+1=a*(B*2) := by
          have hh : (r.val+1)*(B*2)=a*(B*2) := congrArg (fun n => n*(B*2)) hrend
          rw [Nat.add_mul,Nat.mul_comm r.val] at hh
          omega
        rw [he,Nat.mod_self]

 theorem indexCoordinates_next {a B : Nat} (ha : 0<a) (hB : 0<B)
    (t : Fin (a*(B*2))) :
    indexCoordinates hB (successor (Nat.mul_pos ha (by omega)) t)=
      coordinateNext ha hB (indexCoordinates hB t) := by
  rw [←coordinateIndex_reverse hB t,←coordinateIndex_next ha hB]
  simp only [coordinateIndex_inverse]

theorem cycle_step {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (t : Fin (a*(B*2))) :
    SameEdge (cycle (by omega) (by omega) t,
      cycle (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t))
      (ownedEdge (by omega) (by omega) ⟨0,by decide⟩
        (coordinateLabel (by omega) (indexCoordinates (by omega) t)).1
        (coordinateLabel (by omega) (indexCoordinates (by omega) t)).2.1
        (coordinateLabel (by omega) (indexCoordinates (by omega) t)).2.2) := by
  unfold cycle
  rw [indexCoordinates_next (show 0<a by omega) (show 0<B by omega)]
  exact coordinate_step ha hB heven _

theorem torusAdjacent_symm {A B : Nat} (hA : 0<A) (hB : 0<B)
    {u v : Fin A × Fin B} (h : TorusAdjacent hA hB u v) : TorusAdjacent hA hB v u := by
  rcases h with ⟨hy,hx|hx⟩ | ⟨hx,hy|hy⟩
  · exact Or.inl ⟨hy.symm,Or.inr hx⟩
  · exact Or.inl ⟨hy.symm,Or.inl hx⟩
  · exact Or.inr ⟨hx.symm,Or.inr hy⟩
  · exact Or.inr ⟨hx.symm,Or.inl hy⟩

theorem torusAdjacent_sameEdge {A B : Nat} (hA : 0<A) (hB : 0<B)
    {e f : (Fin A × Fin B) × (Fin A × Fin B)}
    (hR : TorusAdjacent hA hB e.1 e.2) (h : SameEdge e f) :
    TorusAdjacent hA hB f.1 f.2 := by
  rcases h with h | h
  · simpa only [h] using hR
  · have hh := torusAdjacent_symm hA hB hR
    simpa only [h] using hh

theorem cycle_adjacent {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (t : Fin (a*(B*2))) :
    TorusAdjacent (show 0<2*a by omega) (show 0<B by omega)
      (cycle (by omega) (by omega) t)
      (cycle (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t)) := by
  exact torusAdjacent_sameEdge _ _ (ownedEdge_adjacent (by omega) (by omega) _ _ _ _)
    (sameEdge_symm (cycle_step ha hB heven t))

/-- Every edge of AOT color zero is realized by an actual forced cyclic step. -/
theorem cycle_covers_colorZero {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (axis : Bool) (r : Fin a) (j : Fin B) :
    ∃ t : Fin (a*(B*2)), SameEdge
      (cycle (by omega) (by omega) t,
       cycle (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t))
      (ownedEdge (by omega) (by omega) ⟨0,by decide⟩ axis r j) := by
  obtain ⟨p,hp⟩ := coordinateLabel_surjective (show 0<a by omega) (axis,r,j)
  obtain ⟨t,ht⟩ := indexCoordinates_surjective (show 0<B by omega) p
  refine ⟨t,?_⟩
  have hh := cycle_step ha hB heven t
  simpa only [ht,hp] using hh

/-- Translation in the first cyclic coordinate preserves actual adjacency. -/
theorem translated_adjacent {A B : Nat} (hA : 0<A) (hB : 0<B)
    {u v : Fin A × Fin B} (h : TorusAdjacent hA hB u v) :
    TorusAdjacent hA hB (successor hA u.1,u.2) (successor hA v.1,v.2) := by
  rcases h with ⟨hy,hx|hx⟩ | ⟨hx,hy|hy⟩
  · exact Or.inl ⟨hy,Or.inl (congrArg (successor hA) hx)⟩
  · exact Or.inl ⟨hy,Or.inr (congrArg (successor hA) hx)⟩
  · exact Or.inr ⟨congrArg (successor hA) hx,Or.inl hy⟩
  · exact Or.inr ⟨congrArg (successor hA) hx,Or.inr hy⟩

theorem translatedCycle_adjacent {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (t : Fin (a*(B*2))) :
    TorusAdjacent (show 0<2*a by omega) (show 0<B by omega)
      (translatedCycle (by omega) (by omega) t)
      (translatedCycle (by omega) (by omega)
        (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t)) :=
  translated_adjacent _ _ (cycle_adjacent ha hB heven t)

/-- The first-coordinate parity of the source of a color-zero arc. -/
def sourceBit {B : Nat} (axis : Bool) (j : Fin B) : Fin 2 :=
  if axis then (if j.val=B-1 then ⟨1,by decide⟩ else ⟨0,by decide⟩)
  else rowParity (j.val+1) ⟨0,by decide⟩

 theorem origin_zero {a B : Nat} (axis : Bool) (r : Fin a) (j : Fin B) :
    origin (⟨0,by decide⟩ : Fin 2) axis r j=(pairEncode (r,sourceBit axis j),j) := by
  cases axis <;> simp [origin,sourceBit,Fin.rev]

 theorem origin_one {a B : Nat} (axis : Bool) (r : Fin a) (j : Fin B) :
    origin (⟨1,by decide⟩ : Fin 2) axis r j=(pairEncode (r,(sourceBit axis j).rev),j) := by
  cases axis
  · by_cases hp : (j.val+1)%2=0 <;> simp [origin,sourceBit,rowParity,hp,Fin.rev]
  · by_cases hj : j.val=B-1 <;> simp [origin,sourceBit,hj,Fin.rev]

 theorem successor_pairEncode {a : Nat} (ha : 0<a) (r : Fin a) (b : Fin 2) :
    successor (show 0<2*a by omega) (pairEncode (r,b))=
      pairEncode (if b.val=0 then r else successor ha r,b.rev) := by
  have hr := r.isLt; have hb := b.isLt
  by_cases hb0 : b.val=0
  · have hbf : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb0
    subst b
    apply Fin.ext
    simp [successor,pairEncode,Fin.rev]
    exact Nat.mod_eq_of_lt (by omega)
  · have hbval : b.val=1 := by omega
    have hbf : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext hbval
    subst b
    apply Fin.ext
    simp [successor,pairEncode,Fin.rev]
    by_cases hrnext : r.val+1<a
    · rw [Nat.mod_eq_of_lt hrnext,Nat.mod_eq_of_lt (show 2*r.val+1+1<2*a by omega)]
      omega
    · have he : r.val+1=a := by omega
      have he' : 2*r.val+1+1=2*a := by omega
      simp [he,he']

/-- Translation by one swaps the two concrete AOT edge-source parities. -/
def translatedBlock {a B : Nat} (ha : 0<a) (axis : Bool) (r : Fin a) (j : Fin B) : Fin a :=
  if (sourceBit axis j).val=0 then r else successor ha r

theorem origin_translate {a B : Nat} (ha : 0<a) (axis : Bool) (r : Fin a) (j : Fin B) :
    (successor (show 0<2*a by omega) (origin (⟨0,by decide⟩ : Fin 2) axis r j).1,
      (origin (⟨0,by decide⟩ : Fin 2) axis r j).2)=
    origin (⟨1,by decide⟩ : Fin 2) axis (translatedBlock ha axis r j) j := by
  rw [origin_zero,origin_one]
  exact Prod.ext (successor_pairEncode ha r (sourceBit axis j)) rfl

theorem translatedBlock_surjective {a B : Nat} (ha : 0<a) (axis : Bool) (j : Fin B) :
    Function.Surjective (fun r => translatedBlock ha axis r j) := by
  intro r
  by_cases hb : (sourceBit axis j).val=0
  · exact ⟨r,by simp [translatedBlock,hb]⟩
  · exact ⟨predecessor ha r,by simp [translatedBlock,hb,successor_predecessor]⟩

def shiftVertex {a B : Nat} (ha : 0<a) (u : Fin (2*a) × Fin B) :=
  (successor (show 0<2*a by omega) u.1,u.2)

def shiftEdge {a B : Nat} (ha : 0<a)
    (e : (Fin (2*a) × Fin B) × (Fin (2*a) × Fin B)) :=
  (shiftVertex ha e.1,shiftVertex ha e.2)

theorem shiftEdge_sameEdge {a B : Nat} (ha : 0<a)
    {e f : (Fin (2*a) × Fin B) × (Fin (2*a) × Fin B)} (h : SameEdge e f) :
    SameEdge (shiftEdge ha e) (shiftEdge ha f) := by
  rcases h with h | h
  · exact Or.inl (congrArg (shiftEdge ha) h)
  · apply Or.inr
    rw [h]
    rfl

theorem ownedEdge_translate {a B : Nat} (ha : 0<a) (hB : 0<B)
    (axis : Bool) (r : Fin a) (j : Fin B) :
    shiftEdge ha (ownedEdge ha hB ⟨0,by decide⟩ axis r j)=
      ownedEdge ha hB ⟨1,by decide⟩ axis (translatedBlock ha axis r j) j := by
  have hax (u : Fin (2*a) × Fin B) :
      shiftEdge ha (axisEdge (show 0<2*a by omega) hB axis u)=
      axisEdge (show 0<2*a by omega) hB axis (shiftVertex ha u) := by
    cases axis <;> rfl
  unfold ownedEdge
  rw [hax]
  have ho := origin_translate ha axis r j
  change shiftVertex ha (origin (⟨0,by decide⟩ : Fin 2) axis r j)=_ at ho
  rw [ho]

theorem translatedCycle_step {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (t : Fin (a*(B*2))) :
    SameEdge (translatedCycle (by omega) (by omega) t,
      translatedCycle (by omega) (by omega)
        (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t))
      (ownedEdge (by omega) (by omega) ⟨1,by decide⟩
        (coordinateLabel (by omega) (indexCoordinates (by omega) t)).1
        (translatedBlock (by omega)
          (coordinateLabel (by omega) (indexCoordinates (by omega) t)).1
          (coordinateLabel (by omega) (indexCoordinates (by omega) t)).2.1
          (coordinateLabel (by omega) (indexCoordinates (by omega) t)).2.2)
        (coordinateLabel (by omega) (indexCoordinates (by omega) t)).2.2) := by
  have h := shiftEdge_sameEdge (show 0<a by omega) (cycle_step ha hB heven t)
  rw [ownedEdge_translate] at h
  exact h

theorem translatedCycle_covers_colorOne {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (axis : Bool) (r : Fin a) (j : Fin B) :
    ∃ t : Fin (a*(B*2)), SameEdge
      (translatedCycle (by omega) (by omega) t,
       translatedCycle (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t))
      (ownedEdge (by omega) (by omega) ⟨1,by decide⟩ axis r j) := by
  obtain ⟨s,hs⟩ := translatedBlock_surjective (show 0<a by omega) axis j r
  change translatedBlock (show 0<a by omega) axis s j=r at hs
  obtain ⟨t,ht⟩ := cycle_covers_colorZero ha hB heven axis s j
  refine ⟨t,?_⟩
  have hh := shiftEdge_sameEdge (show 0<a by omega) ht
  rw [ownedEdge_translate,hs] at hh
  exact hh

/-- Both explicit Hamilton tours together cover every actual torus edge. -/
theorem HamiltonPair_cover {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (u v : Fin (2*a) × Fin B) (h : TorusAdjacent (by omega) (by omega) u v) :
    (∃ t : Fin (a*(B*2)), SameEdge
      (cycle (by omega) (by omega) t,
       cycle (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t)) (u,v)) ∨
    (∃ t : Fin (a*(B*2)), SameEdge
      (translatedCycle (by omega) (by omega) t,
       translatedCycle (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t)) (u,v)) := by
  obtain ⟨c,axis,r,j,hown⟩ := ownedEdge_cover (show 0<a by omega) (show 0<B by omega) u v h
  have hc := c.isLt
  by_cases hc0 : c.val=0
  · have hcf : c=(⟨0,by decide⟩ : Fin 2) := Fin.ext hc0
    subst c
    obtain ⟨t,ht⟩ := cycle_covers_colorZero ha hB heven axis r j
    exact Or.inl ⟨t,sameEdge_trans ht hown⟩
  · have hcv : c.val=1 := by omega
    have hcf : c=(⟨1,by decide⟩ : Fin 2) := Fin.ext hcv
    subst c
    obtain ⟨t,ht⟩ := translatedCycle_covers_colorOne ha hB heven axis r j
    exact Or.inr ⟨t,sameEdge_trans ht hown⟩

/-- The two actual Hamilton tours have no common undirected edge. -/
theorem HamiltonPair_disjoint {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0)
    (s t : Fin (a*(B*2))) :
    ¬SameEdge
      (cycle (by omega) (by omega) s,
       cycle (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (by omega)) s))
      (translatedCycle (by omega) (by omega) t,
       translatedCycle (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t)) := by
  intro h
  have hh := sameEdge_trans (sameEdge_symm (cycle_step ha hB heven s))
    (sameEdge_trans h (translatedCycle_step ha hB heven t))
  have hu := ownedEdge_unique ha (show 3≤B by omega) _ _ _ _ _ _ _ _ hh
  have hc := congrArg Fin.val hu.1
  change (0:Nat)=1 at hc
  omega

theorem simpleCycle_step_unique {V : Type} {N : Nat} (hN : 3≤N)
    (f : Fin N → V) (hinj : Function.Injective f) (s t : Fin N)
    (h : SameEdge (f s,f (successor (by omega) s))
      (f t,f (successor (by omega) t))) : s=t := by
  apply cyclic_arc_unique hN
  rcases h with h | h
  · exact Or.inl (Prod.ext (hinj (congrArg Prod.fst h)) (hinj (congrArg Prod.snd h)))
  · exact Or.inr (Prod.ext (hinj (congrArg Prod.fst h)) (hinj (congrArg Prod.snd h)))

/-- A complete uniform Hamilton decomposition of the even rectangular torus.
The successor is forced to be addition by one modulo the full cycle length. -/
theorem evenTorusHamiltonDecomposition {a B : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) :
    ∃ tour : Bool → Fin (a*(B*2)) → Fin (2*a) × Fin B,
      (∀ p, Function.Injective (tour p)) ∧
      (∀ p, Function.Surjective (tour p)) ∧
      (∀ p t, TorusAdjacent (show 0<2*a by omega) (show 0<B by omega)
        (tour p t) (tour p (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t))) ∧
      (∀ u v, TorusAdjacent (show 0<2*a by omega) (show 0<B by omega) u v →
        ∃ p t, SameEdge (tour p t,
          tour p (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t)) (u,v)) ∧
      (∀ p q s t, SameEdge
        (tour p s,tour p (successor (Nat.mul_pos (show 0<a by omega) (by omega)) s))
        (tour q t,tour q (successor (Nat.mul_pos (show 0<a by omega) (by omega)) t)) → p=q ∧ s=t) := by
  let tour : Bool → Fin (a*(B*2)) → Fin (2*a) × Fin B :=
    fun p => if p then translatedCycle (show 0<a by omega) (show 0<B by omega)
      else cycle (show 0<a by omega) (show 0<B by omega)
  have hsize : 3≤a*(B*2) := by
    have hm : 2*8≤a*(B*2) := Nat.mul_le_mul ha (by omega)
    omega
  have hinj : ∀ p, Function.Injective (tour p) := by
    intro p; cases p
    · exact cycle_injective _ _
    · exact translatedCycle_injective _ _
  refine ⟨tour,hinj,?_,?_,?_,?_⟩
  · intro p; cases p
    · exact cycle_surjective _ _
    · exact translatedCycle_surjective _ _
  · intro p t; cases p
    · exact cycle_adjacent ha hB heven t
    · exact translatedCycle_adjacent ha hB heven t
  · intro u v h
    rcases HamiltonPair_cover ha hB heven u v h with ⟨t,ht⟩ | ⟨t,ht⟩
    · exact ⟨false,t,ht⟩
    · exact ⟨true,t,ht⟩
  · intro p q s t h
    cases p <;> cases q
    · exact ⟨rfl,simpleCycle_step_unique hsize _ (hinj false) s t h⟩
    · exact False.elim (HamiltonPair_disjoint ha hB heven s t h)
    · exact False.elim (HamiltonPair_disjoint ha hB heven t s (sameEdge_symm h))
    · exact ⟨rfl,simpleCycle_step_unique hsize _ (hinj true) s t h⟩

#print axioms evenTorusHamiltonDecomposition
#print axioms ownedEdge_translate
#print axioms translatedCycle_step
#print axioms HamiltonPair_cover
#print axioms HamiltonPair_disjoint
#print axioms coordinateLabel_injective
#print axioms coordinateLabel_surjective
#print axioms indexCoordinates_next
#print axioms cycle_step
#print axioms cycle_adjacent
#print axioms cycle_covers_colorZero
#print axioms translatedCycle_adjacent
#print axioms coordinate_step
#print axioms ownedEdge_adjacent
#print axioms balancedEdge_covers_labels
#print axioms translatedCycle_injective
#print axioms translatedCycle_surjective
#print axioms cycle_injective
#print axioms cycle_surjective
#print axioms ownedEdge_cover
#print axioms ownedEdge_unique
#print axioms balancedEdge_list_nodup
#print axioms uniform_subdivision_count
#print axioms vertex_injective
#print axioms vertex_surjective
#print axioms translatedVertex_injective
#print axioms translatedVertex_surjective
end ErdePaths.Wiggle
