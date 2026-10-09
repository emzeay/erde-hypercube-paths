import ErdePaths.HamiltonData

namespace ErdePaths.BaseHamilton
open HamiltonData SquareLift

/-- The literal 0,1,3,2 Hamilton order of Q₂. -/
def gray (t : Fin 4) : Vertex 2 :=
  ⟨if t.val<2 then t.val else 5-t.val,by have := t.isLt; split <;> omega⟩

theorem gray_inverse : ∀ t : Fin 4, gray (gray t)=t := by decide

def cycle : CycleData (Vertex 2) (@Adjacent 2) 4 (by decide) where
  cycle := gray
  position := gray
  position_cycle := gray_inverse
  cycle_position := gray_inverse
  adjacent := by decide

/-- The necessary induction base, kernel decided on the exact four-vertex
cube. It is not experimental evidence or a substitute for uniform induction. -/
def decomposition : DecompositionData (Vertex 2) (@Adjacent 2) 1 4 (by decide) where
  cycles := fun _ => cycle
  symmetric := fun _ _ h => adjacent_symm h
  loopfree := fun v h => adjacent_ne h rfl
  cover := by
    simp only [SameEdge]
    decide
  unique := by
    simp only [SameEdge]
    decide

#print axioms decomposition
end ErdePaths.BaseHamilton
