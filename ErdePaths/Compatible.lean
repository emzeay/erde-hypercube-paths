import ErdePaths.Basic

namespace ErdePaths

/-- Equality of an undirected edge, permitting reversed endpoints. -/
def UndirectedEq {V : Type} (e f : V × V) : Prop := e = f ∨ e = (f.2,f.1)

/-- A finite indexed path partition in a graph, with unique edge positions.
The explicit index list witnesses finiteness; vertices may occur in several paths. -/
structure GraphPathDecomposition (V : Type) (R : V → V → Prop) (L : Nat) where
  Index : Type
  indices : List Index
  vertices : Index → Fin (L+1) → V
  simple : ∀ p, p ∈ indices → Function.Injective (vertices p)
  adjacent : ∀ p, p ∈ indices → ∀ j : Fin L,
    R (vertices p j.castSucc) (vertices p j.succ)
  cover : ∀ u v, R u v → ∃ p, p ∈ indices ∧ ∃ j : Fin L,
    UndirectedEq (vertices p j.castSucc,vertices p j.succ) (u,v)
  unique : ∀ p q, p ∈ indices → q ∈ indices → ∀ j k : Fin L,
    UndirectedEq (vertices p j.castSucc,vertices p j.succ)
      (vertices q k.castSucc,vertices q k.succ) → p = q ∧ j = k

/-- A faithful directed-compatible Hamilton-factor/path partition.
A cycle is indexed cyclically by Fin N. Each path step is explicitly assigned
to one factor and one clockwise cycle arc, and that assignment is a bijection
between all path positions and all factor arc positions. -/
structure CompatibleDecomposition (V : Type) (R : V → V → Prop) (N L : Nat) where
  positive : 0 < N
  symmetric : ∀ u v, R u v → R v u
  factorCount : Nat
  pathCount : Nat
  cycle : Fin factorCount → Fin N → V
  cycle_injective : ∀ f, Function.Injective (cycle f)
  cycle_surjective : ∀ f, Function.Surjective (cycle f)
  /-- Clockwise successor of the last cycle coordinate wraps to zero. -/
  next : Fin N → Fin N
  next_eq : ∀ i, (next i).val = (i.val+1) % N
  cycle_adjacent : ∀ f i, R (cycle f i) (cycle f (next i))
  factor_cover : ∀ u v, R u v → ∃ f i,
    UndirectedEq (cycle f i,cycle f (next i)) (u,v)
  factor_unique : ∀ f i g j,
    UndirectedEq (cycle f i,cycle f (next i)) (cycle g j,cycle g (next j)) →
      f = g ∧ i = j
  path : Fin pathCount → Fin (L+1) → V
  path_injective : ∀ p, Function.Injective (path p)
  edgeFactor : Fin pathCount → Fin L → Fin factorCount
  phase : Fin pathCount → Fin L → Fin N
  source : ∀ p j, cycle (edgeFactor p j) (phase p j) = path p j.castSucc
  target : ∀ p j, cycle (edgeFactor p j) (next (phase p j)) = path p j.succ
  position_cover : ∀ f i, ∃ p j, edgeFactor p j = f ∧ phase p j = i
  position_unique : ∀ p j q k, edgeFactor p j = edgeFactor q k →
    phase p j = phase q k → p = q ∧ j = k

/-- The compatibility interface entails an actual path partition; none of its
cycle/path labeling data is accepted without endpoint and graph-edge checks. -/
def CompatibleDecomposition.toGraphPathDecomposition {V : Type} {R : V → V → Prop}
    {N L : Nat} (d : CompatibleDecomposition V R N L) : GraphPathDecomposition V R L where
  Index := Fin d.pathCount
  indices := List.ofFn id
  vertices := d.path
  simple := fun p _ => d.path_injective p
  adjacent := by
    intro p _ j
    have h := d.cycle_adjacent (d.edgeFactor p j) (d.phase p j)
    simpa only [d.source,d.target] using h
  cover := by
    intro u v huv
    obtain ⟨f,i,he⟩ := d.factor_cover u v huv
    obtain ⟨p,j,hf,hi⟩ := d.position_cover f i
    refine ⟨p,by simp [List.mem_ofFn],j,?_⟩
    have hs := d.source p j
    have ht := d.target p j
    rw [hf,hi] at hs ht
    simpa only [hs,ht] using he
  unique := by
    intro p q _ _ j k he
    have hh : UndirectedEq
        (d.cycle (d.edgeFactor p j) (d.phase p j),
          d.cycle (d.edgeFactor p j) (d.next (d.phase p j)))
        (d.cycle (d.edgeFactor q k) (d.phase q k),
          d.cycle (d.edgeFactor q k) (d.next (d.phase q k))) := by
      simpa only [d.source,d.target] using he
    have hpos := d.factor_unique _ _ _ _ hh
    exact d.position_unique p j q k hpos.1 hpos.2

#print axioms CompatibleDecomposition.toGraphPathDecomposition
end ErdePaths
