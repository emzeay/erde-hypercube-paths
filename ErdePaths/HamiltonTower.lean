import ErdePaths.HamiltonSquare

namespace ErdePaths.HamiltonTower
open SourceClock HamiltonData HamiltonSquare SquareLift

def count (m : Nat) : Nat→Nat
  | 0 => m
  | k+1 => 2*count m k

def relation {V : Type} (R : V→V→Prop) : (k : Nat)→VertexPower V k→VertexPower V k→Prop
  | 0 => R
  | k+1 => ProductAdjacent (relation R k)

theorem length_four {N : Nat} (h4 : 4≤N) (k : Nat) : 4≤lengthPower N k := by
  induction k with
  | zero => exact h4
  | succ k ih =>
    have hm := Nat.mul_le_mul_left (lengthPower N k) (show 1≤lengthPower N k by omega)
    simp only [Nat.mul_one] at hm
    exact Nat.le_trans ih hm

/-- Actual recursive product Hamilton partitions at every depth. -/
def decomposition {V : Type} {R : V→V→Prop} {m N : Nat} {hN : 0<N}
    (D : DecompositionData V R m N hN) (h4 : 4≤N) :
    (k : Nat)→DecompositionData (VertexPower V k) (relation R k) (count m k)
      (lengthPower N k) (lengthPower_positive hN k)
  | 0 => D
  | k+1 => HamiltonSquare.square (decomposition D h4 k) (length_four h4 k)

/-- Boolean source choices identify actual factors of the recursive partition. -/
def code {m : Nat} : (k : Nat)→Fin m→(Fin k→Bool)→Fin (count m k)
  | 0,f,_ => f
  | k+1,f,address => factorIndex (code k f (fun i => address i.castSucc),address (Fin.last k))

theorem code_surjective {m : Nat} (k : Nat) (q : Fin (count m k)) :
    ∃f address, code k f address=q := by
  induction k with
  | zero => exact ⟨q,fun i => Fin.elim0 i,rfl⟩
  | succ k ih =>
    change Fin (2*count m k) at q
    obtain ⟨f,a,ha⟩ := ih (factorCoordinates q).1
    let address : Fin (k+1)→Bool := Fin.lastCases (factorCoordinates q).2 a
    refine ⟨f,address,?_⟩
    simp only [code,address,Fin.lastCases_castSucc,Fin.lastCases_last]
    rw [ha]
    exact factorIndex_coordinates q

theorem code_injective {m : Nat} (k : Nat) (f g : Fin m) (a b : Fin k→Bool)
    (he : code k f a=code k g b) : f=g ∧ a=b := by
  induction k with
  | zero => exact ⟨he,funext (fun i => Fin.elim0 i)⟩
  | succ k ih =>
    have hc := congrArg factorCoordinates he
    simp only [code,factorCoordinates_index] at hc
    obtain ⟨hf,ha⟩ := ih _ _ (congrArg Prod.fst hc)
    refine ⟨hf,?_⟩
    funext i
    refine Fin.lastCases (congrArg Prod.snd hc) (fun j => congrFun ha j) i

/-- The actual recursively owned factor has precisely the source inverse clock
used by the uniform low-bit decoder. No independent clock oracle is supplied. -/
theorem clock_eq {V : Type} {R : V→V→Prop} {m N : Nat} {hN : 0<N}
    (D : DecompositionData V R m N hN) (h4 : 4≤N)
    (k : Nat) (f : Fin m) (address : Fin k→Bool) :
    ((decomposition D h4 k).cycles (code k f address)).toClockData=
      iteratedClock hN (D.cycles f).toClockData k address := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [decomposition,code,HamiltonSquare.square,factorCoordinates_index,
      HamiltonSquare.cycle,iteratedClock]
    rw [ih]

#print axioms decomposition
#print axioms code_surjective
#print axioms clock_eq
end ErdePaths.HamiltonTower
