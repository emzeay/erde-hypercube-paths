import ErdePaths.AACTransition

namespace ErdePaths.AACEdge
open AACTransition SquareLift

/-- The actual incoming coarse edge, retaining cyclic-edge identity even when
coarse grids have parallel edges. -/
def incoming {K B : Nat} (hK : 0<K) (hB : 0<B) (s : State K B) : Grid K B ⊕ Grid K B :=
  match s.2.2 with
  | .up => .inl (s.1,s.2.1)
  | .down => .inl (predecessor hK s.1,s.2.1)
  | .right => .inr (s.1,s.2.1)
  | .left => .inr (s.1,predecessor hB s.2.1)

theorem cross_incoming {K B : Nat} (hK : 0<K) (hB : 0<B) (s : State K B) :
    incoming hK hB (cross hK hB s)=incoming hK hB s := by
  rcases s with ⟨i,j,p⟩
  cases p <;> simp [incoming,cross,predecessor_successor]

theorem incoming_surjective {K B : Nat} (hK : 0<K) (hB : 0<B) :
    Function.Surjective (incoming hK hB) := by
  intro e
  cases e with
  | inl e => exact ⟨(e.1,e.2,.up),rfl⟩
  | inr e => exact ⟨(e.1,e.2,.right),rfl⟩

/-- Every label has exactly the two oppositely directed incoming states. This
is label identity, not a false simplicity claim for a size-two coarse cycle. -/
theorem incoming_fiber {K B : Nat} (hK : 0<K) (hB : 0<B) (s t : State K B)
    (he : incoming hK hB s=incoming hK hB t) : s=t ∨ s=cross hK hB t := by
  have hpK (i j : Fin K) : predecessor hK i=predecessor hK j ↔ i=j := by
    constructor
    · intro hh
      have hh' := congrArg (successor hK) hh
      simpa only [successor_predecessor] using hh'
    · intro hh; exact congrArg (predecessor hK) hh
  have hpB (i j : Fin B) : predecessor hB i=predecessor hB j ↔ i=j := by
    constructor
    · intro hh
      have hh' := congrArg (successor hB) hh
      simpa only [successor_predecessor] using hh'
    · intro hh; exact congrArg (predecessor hB) hh
  rcases s with ⟨i,j,p⟩
  rcases t with ⟨i',j',q⟩
  cases p <;> cases q <;> simp only [incoming,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,
    reduceCtorEq,hpK,hpB] at he
  all_goals try contradiction
  all_goals rcases he with ⟨hi,hj⟩
  all_goals simp_all [cross,Prod.mk.injEq]
  · rw [←hi,successor_predecessor]
  · rw [←hj,successor_predecessor]

#print axioms incoming_fiber
end ErdePaths.AACEdge
