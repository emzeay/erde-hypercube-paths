import ErdePaths.AACFineClock
import ErdePaths.DenseSourceMarks

namespace ErdePaths.AACFineGeometry
open SquareLift AACTransition AACFine AACFineClock

/-- A literal fine point outside the coarse grid. -/
def NonGrid {K A B : Nat} (hA : 0<A) (v : Fine K A B) : Prop :=
  ∀ g : Grid K B, v≠gridPoint hA g

/-- Only the two base-cycle neighbors are incident to an unanchored fine point. -/
theorem nonGrid_neighbors {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {v w : Fine K A B} (hv : NonGrid hA v) (he : AACTransition.Adjacent hK hA hB v w) :
    w=(successor (Nat.mul_pos hK hA) v.1,v.2) ∨
    w=(predecessor (Nat.mul_pos hK hA) v.1,v.2) := by
  obtain ⟨e,he⟩ := he
  cases e with
  | inl p =>
    rcases p with ⟨x,j⟩
    rcases he with he|he
    · have hx := congrArg (fun p => p.1.1) he
      have hj := congrArg (fun p => p.1.2) he
      have hw := congrArg Prod.snd he
      simp only [AACTransition.decode] at hx hj hw
      left
      simpa only [←hx,←hj] using hw.symm
    · have hx := congrArg (fun p => p.2.1) he
      have hj := congrArg (fun p => p.2.2) he
      have hw := congrArg Prod.fst he
      simp only [AACTransition.decode] at hx hj hw
      right
      rw [←hx,←hj,predecessor_successor]
      exact hw.symm
  | inr p =>
    rcases p with ⟨i,j⟩
    rcases he with he|he
    · exact False.elim (hv (i,j) (congrArg Prod.fst he).symm)
    · exact False.elim (hv (i,successor hB j) (congrArg Prod.snd he).symm)

/-- The residue-zero characterization uses the actual mixed-radix encoding. -/
theorem nonGrid_iff {K A B : Nat} (hA : 0<A) (v : Fine K A B) :
    NonGrid hA v ↔ v.1.val%A≠0 := by
  constructor
  · intro hv hz
    have he : AnchoredEmbedding.positionEncode
      (AnchoredEmbedding.positionDecode hA v.1).1 ⟨0,hA⟩=v.1 := by
      have hd : (AnchoredEmbedding.positionDecode hA v.1).2=⟨0,hA⟩ := by
        apply Fin.ext
        exact hz
      rw [←hd]
      exact AnchoredEmbedding.positionEncode_decode hA v.1
    exact hv ((AnchoredEmbedding.positionDecode hA v.1).1,v.2) (Prod.ext he.symm rfl)
  · intro hv g he
    have hx := congrArg (fun v => v.1.val%A) he
    simp only [gridPoint,AnchoredEmbedding.positionEncode,Nat.add_zero,Nat.mul_mod_right] at hx
    exact hv hx

/-- In an edge-unique cyclic traversal a degree-two vertex cannot recur.
The graph condition is supplied below by literal fine geometry. -/
theorem degreeTwo_occurrence_unique {V : Type} {E : Nat} (hE : 0<E) (h2 : 2≤E)
    (f : Fin E→V)
    (unique : ∀n m, SameEdge (f n,f (successor hE n))
      (f m,f (successor hE m)) → n=m)
    {v a b : V} (ha : a≠v) (hb : b≠v)
    (neighbors : ∀n, f n=v →
      (f (successor hE n)=a ∨ f (successor hE n)=b) ∧
      (f (predecessor hE n)=a ∨ f (predecessor hE n)=b))
    (n m : Fin E) (hn : f n=v) (hm : f m=v) : n=m := by
  have hd : f (predecessor hE n)≠f (successor hE n) := by
    intro he
    have hh := unique (predecessor hE n) n (Or.inr (by
      simp only [successor_predecessor]
      rw [he,hn]))
    have hs := congrArg (successor hE) hh
    rw [successor_predecessor] at hs
    exact successor_ne hE h2 n hs.symm
  have incne : f (predecessor hE n)≠v := by
    rcases (neighbors n hn).2 with h|h
    · rw [h]; exact ha
    · rw [h]; exact hb
  have casesOut : f (successor hE m)=f (successor hE n) ∨
      f (successor hE m)=f (predecessor hE n) := by
    rcases (neighbors n hn).1 with ho|ho <;>
      rcases (neighbors n hn).2 with hi|hi <;>
      rcases (neighbors m hm).1 with hm'|hm'
    all_goals first
      | exact Or.inl (hm'.trans ho.symm)
      | exact Or.inr (hm'.trans hi.symm)
      | exact False.elim (hd (hi.trans ho.symm))
  rcases casesOut with he|he
  · exact unique n m (Or.inl (Prod.ext (hn.trans hm.symm) he.symm))
  · have hmn := unique m (predecessor hE n) (Or.inr (by
      simp only [successor_predecessor]
      exact Prod.ext (hm.trans hn.symm) he))
    rw [hmn] at hm
    exact False.elim (incne hm)

/-- The actual constructed fine clock visits each non-grid point at most once.
No vertex-injectivity hypothesis is imposed on the Euler clock. -/
theorem nonGrid_clock_collision {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel hK hA hB C hE))
    (n m : Fin E) (hv : NonGrid hA (fineVertex hK hA hB C hE n))
    (he : fineVertex hK hA hB C hE n=fineVertex hK hA hB C hE m) : n=m := by
  let f := fineVertex hK hA hB C hE
  let v := f n
  let a : Fine K A B := (successor (Nat.mul_pos hK hA) v.1,v.2)
  let b : Fine K A B := (predecessor (Nat.mul_pos hK hA) v.1,v.2)
  have ha : a≠v := by
    intro h
    exact successor_ne (Nat.mul_pos hK hA) (by omega) v.1 (congrArg Prod.fst h)
  have hb : b≠v := by
    intro h
    have hs := congrArg (successor (Nat.mul_pos hK hA)) (congrArg Prod.fst h)
    rw [successor_predecessor] at hs
    exact successor_ne (Nat.mul_pos hK hA) (by omega) v.1 hs.symm
  apply degreeTwo_occurrence_unique hpos hE2 f
    (numeric_physical_unique hK hA hB h3 hB3 C hE hpos hinj) ha hb
  · intro j hj
    have out : AACTransition.Adjacent hK hA hB (f j) (f (successor hpos j)) :=
      ⟨fineLabel hK hA hB C hE j,fineVertex_step hK hA hB C hE hpos j⟩
    have inc : AACTransition.Adjacent hK hA hB (f j) (f (predecessor hpos j)) := by
      refine ⟨fineLabel hK hA hB C hE (predecessor hpos j),?_⟩
      have hs := fineVertex_step hK hA hB C hE hpos (predecessor hpos j)
      rw [successor_predecessor] at hs
      rcases hs with hs|hs
      · exact Or.inr hs
      · exact Or.inl hs
    rw [hj] at out inc
    exact ⟨nonGrid_neighbors hK hA hB hv out,nonGrid_neighbors hK hA hB hv inc⟩
  · rfl
  · exact he.symm

/-- Literal internal representative offsets are therefore unique occurrences. -/
theorem internal_clock_collision {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel hK hA hB C hE))
    (i : Fin K) (z : Fin A) (hz : 0<z.val) (j : Fin B) (n m : Fin E)
    (hn : fineVertex hK hA hB C hE n=(AnchoredEmbedding.positionEncode i z,j))
    (hm : fineVertex hK hA hB C hE m=(AnchoredEmbedding.positionEncode i z,j)) : n=m := by
  apply nonGrid_clock_collision hK hA hB h3 hB3 C hE hpos hE2 hinj n m
  · apply (nonGrid_iff hA _).2
    rw [hn]
    simp only [AnchoredEmbedding.positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt z.isLt]
    omega
  · exact hn.trans hm.symm

/-- Fine edge cover already supplies an actual clock occurrence of every
fine vertex, including all future internal marks. -/
theorem fineVertex_surjective {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E)
    (hsur : Function.Surjective (fineLabel hK hA hB C hE)) :
    Function.Surjective (fineVertex hK hA hB C hE) := by
  intro v
  obtain ⟨n,hn⟩ := hsur (Sum.inl v)
  have hs := fineVertex_step hK hA hB C hE hpos n
  rw [hn] at hs
  rcases hs with hs|hs
  · exact ⟨n,(congrArg Prod.fst hs).symm⟩
  · exact ⟨successor hpos n,(congrArg Prod.fst hs).symm⟩

/-- Each literal internal point has one genuine numeric Euler occurrence. -/
theorem internal_clock_owner {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel hK hA hB C hE))
    (hsur : Function.Surjective (fineLabel hK hA hB C hE))
    (i : Fin K) (z : Fin A) (hz : 0<z.val) (j : Fin B) :
    ∃n : Fin E, fineVertex hK hA hB C hE n=(AnchoredEmbedding.positionEncode i z,j) ∧
      ∀m, fineVertex hK hA hB C hE m=(AnchoredEmbedding.positionEncode i z,j) → m=n := by
  obtain ⟨n,hn⟩ := fineVertex_surjective hK hA hB C hE hpos hsur
    (AnchoredEmbedding.positionEncode i z,j)
  exact ⟨n,hn,fun m hm =>
    internal_clock_collision hK hA hB h3 hB3 C hE hpos hE2 hinj i z hz j m n hm hn⟩

/-- Color of the incident edge at a concrete grid arrival port. The first
axis may change color in its interior; endpoint port colors are literal. -/
def portColor {K B : Nat} (turns : Grid K B→Bool) (s : State K B) : Bool :=
  let row := decide (s.2.1.val%2=1)
  match s.2.2 with
  | .up => row ^^ turns (s.1,s.2.1)
  | .down => !(row ^^ turns (s.1,s.2.1))
  | .right => row
  | .left => !row

theorem pair_color {K B : Nat} (turns : Grid K B→Bool) (s : State K B) :
    portColor turns (atPair turns s)=portColor turns s := by
  rcases s with ⟨i,j,p⟩
  cases ht : turns (i,j) <;> cases hr : decide (j.val%2=1) <;> cases p <;>
    simp [portColor,atPair,pair,ht,hr]

/-- At one physical grid, each color has exactly the two paired ports. -/
theorem same_grid_color {K B : Nat} (turns : Grid K B→Bool) (s u : State K B)
    (hv : stateVertex s=stateVertex u) (hc : portColor turns s=portColor turns u) :
    s=u ∨ s=atPair turns u := by
  rcases s with ⟨i,j,p⟩
  rcases u with ⟨i',j',p'⟩
  have hi := congrArg Prod.fst hv
  have hj := congrArg Prod.snd hv
  simp only [stateVertex] at hi hj
  subst i'; subst j'
  cases ht : turns (i,j) <;> cases hr : decide (j.val%2=1) <;> cases p <;> cases p' <;>
    simp_all [portColor,atPair,pair]

/-- A concrete edge-unique coarse Euler orbit cannot visit the same grid on
the same endpoint color twice. This is the local collision law underlying
opposite-colored AAC intervals. -/
theorem grid_clock_collision_color {K B N : Nat} (hK : 0<K) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hinj : Function.Injective (fun n => AACEdge.incoming hK hB (C.point n)))
    (n m : Fin N) (hv : stateVertex (C.point n)=stateVertex (C.point m))
    (hc : portColor turns (C.point n)=portColor turns (C.point m)) : n=m := by
  rcases same_grid_color turns (C.point n) (C.point m) hv hc with hs|hs
  · exact C.injective hs
  · have hn : AACEdge.incoming hK hB (C.point (successor hN m))=
        AACEdge.incoming hK hB (C.point n) := by
      rw [←C.next m,←atPair_involutive turns (C.point m),←hs]
      simp only [transition,atPair_involutive,AACEdge.cross_incoming]
    have hm := hinj hn
    have hx : cross hK hB (C.point n)=C.point n := by
      have hstep := C.next m
      rw [transition,←hs,hm] at hstep
      exact hstep
    rcases hport : (C.point n).2.2 with p
    cases p <;> have hh := congrArg (fun s => s.2.2) hx <;>
      simp [cross,hport] at hh

theorem segment_grid_offset {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (s : State K B) (k : Fin (weight A s.2.2)) (g : Grid K B)
    (he : segment hK hA hB s k.castSucc=gridPoint hA g) : k.val=0 := by
  have hx := congrArg (fun v => v.1.val%A) he
  have hk := k.isLt
  rcases s with ⟨i,j,port⟩
  cases port
  · have hlt : k.val<A := by simpa only [weight] using hk
    simp only [segment,Fin.val_castSucc,dite_eq_left hlt,gridPoint,
      AnchoredEmbedding.positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt hlt,
      Nat.add_zero,Nat.mul_mod_right] at hx
    exact hx
  · simp only [weight] at hk
    omega
  · have hlt : k.val<A := by simpa only [weight] using hk
    by_cases hz : k.val=0
    · exact hz
    · have hd : A-k.val<A := by omega
      simp only [segment,Fin.val_castSucc,dite_eq_right hz,gridPoint,
        AnchoredEmbedding.positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt hd,
        Nat.add_zero,Nat.mul_mod_right] at hx
      omega
  · simp only [weight] at hk
    omega

theorem expanded_grid_start {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) (g : Grid K B)
    (he : expandedVertex hK hA hB C p=gridPoint hA g) :
    p.2.val=0 ∧ stateVertex (C.point p.1)=g := by
  have hz := segment_grid_offset hK hA hB (atPair turns (C.point p.1)) p.2 g he
  have h0 : p.2.castSucc=⟨0,by have := weight_pos hA (atPair turns (C.point p.1)).2.2; omega⟩ :=
    Fin.ext hz
  change segment hK hA hB (atPair turns (C.point p.1)) p.2.castSucc=_ at he
  rw [h0,segment_start] at he
  have hphys : stateVertex (atPair turns (C.point p.1))=g := by
    apply Prod.ext
    · have hx := congrArg (fun v => (AnchoredEmbedding.positionDecode hA v.1).1) he
      simpa only [gridPoint,AnchoredEmbedding.positionDecode_encode] using hx
    · simpa only [gridPoint] using congrArg Prod.snd he
  exact ⟨hz,by simpa only [atPair,stateVertex] using hphys⟩

/-- Repeated grid vertices in the actual ragged fine expansion have different
endpoint colors; this theorem is independent of any chosen interval partition. -/
theorem expanded_grid_collision_color {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hinj : Function.Injective (fun n => AACEdge.incoming hK hB (C.point n)))
    (p q : ExpandedIndex (A := A) C) (g : Grid K B)
    (hp : expandedVertex hK hA hB C p=gridPoint hA g)
    (hq : expandedVertex hK hA hB C q=gridPoint hA g)
    (hc : portColor turns (C.point p.1)=portColor turns (C.point q.1)) : p=q := by
  have hp' := expanded_grid_start hK hA hB C p g hp
  have hq' := expanded_grid_start hK hA hB C q g hq
  have hi := grid_clock_collision_color hK hB C hinj p.1 q.1
    (hp'.2.trans hq'.2.symm) hc
  rcases p with ⟨i,a⟩
  rcases q with ⟨j,b⟩
  simp only at hi hp' hq'
  subst j
  have hab : a=b := Fin.ext (hp'.1.trans hq'.1.symm)
  subst b
  rfl

/-- All collisions in the numeric fine clock are either identical occurrences
or differently colored visits to a literal coarse grid. -/
theorem fine_clock_collision {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hlabel : Function.Injective (fineLabel hK hA hB C hE))
    (hcoarse : Function.Injective (fun n => AACEdge.incoming hK hB (C.point n)))
    (n m : Fin E) (he : fineVertex hK hA hB C hE n=fineVertex hK hA hB C hE m) :
    n=m ∨ ∃g : Grid K B, fineVertex hK hA hB C hE n=gridPoint hA g ∧
      portColor turns (C.point (exactPosition C hE n).1)≠
        portColor turns (C.point (exactPosition C hE m).1) := by
  classical
  by_cases hg : ∃g : Grid K B, fineVertex hK hA hB C hE n=gridPoint hA g
  · obtain ⟨g,hg⟩ := hg
    by_cases hc : portColor turns (C.point (exactPosition C hE n).1)=
        portColor turns (C.point (exactPosition C hE m).1)
    · left
      apply exactPosition_injective C hE
      exact expanded_grid_collision_color hK hA hB C hcoarse
        (exactPosition C hE n) (exactPosition C hE m) g hg (he.symm.trans hg) hc
    · exact Or.inr ⟨g,hg,hc⟩
  · left
    apply nonGrid_clock_collision hK hA hB h3 hB3 C hE hpos hE2 hlabel n m _ he
    intro g h
    exact hg ⟨g,h⟩

/-- Physical cube-factor transport reflects fine coordinates because both
actual Hamilton clocks have checked position inverses. -/
def physical {U V : Type} {K A B : Nat}
    (G : SourceClock.ClockData U (K*A)) (H : SourceClock.ClockData V B)
    (v : Fine K A B) : U×V := (G.cycle v.1,H.cycle v.2)

theorem physical_injective {U V : Type} {K A B : Nat}
    (G : SourceClock.ClockData U (K*A)) (H : SourceClock.ClockData V B) :
    Function.Injective (physical G H) := by
  intro x y he
  apply Prod.ext
  · have hx := congrArg (fun v => G.position v.1) he
    simpa only [physical,G.position_cycle] using hx
  · have hy := congrArg (fun v => H.position v.2) he
    simpa only [physical,H.position_cycle] using hy

#print axioms internal_clock_owner
#print axioms fine_clock_collision
#print axioms expanded_grid_collision_color
#print axioms physical_injective
#print axioms pair_color
#print axioms grid_clock_collision_color
#print axioms nonGrid_clock_collision
#print axioms internal_clock_collision
end ErdePaths.AACFineGeometry
