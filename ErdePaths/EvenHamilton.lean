import ErdePaths.HamiltonPartition
import ErdePaths.BaseHamilton
import ErdePaths.CubeHierarchy

namespace ErdePaths.EvenHamilton
open HamiltonData HamiltonResidual HamiltonNormalize

/-- Literal integer cube coordinates for appending two binary coordinates. -/
def appendTwo (n : Nat) : CubeHierarchy.Coordinates
    (Vertex n×Fin 4) (ActualGrid (@Adjacent n)) (n+2) where
  encode := @CubeProduct.encode n 2
  decode := @CubeProduct.decode n 2
  decode_encode := @CubeProduct.decode_encode n 2
  encode_decode := @CubeProduct.encode_decode n 2
  adjacent u v := by
    rw [CubeProduct.adjacent_iff]
    exact or_comm

def castData {n n' m m' N N' hN hN'}
    (hd : n=n') (hf : m=m') (hl : N=N')
    (D : DecompositionData (Vertex n) (@Adjacent n) m N hN) :
    DecompositionData (Vertex n') (@Adjacent n') m' N' hN' := by
  subst n'; subst m'; subst N'; exact D

theorem room_three (k : Nat) : 3≤2^(2*(k+1)) := by
  have hd : 2*(k+1)=2*k+2 := by omega
  rw [hd,Nat.pow_add]
  have hp : 0<2^(2*k) := Nat.two_pow_pos _
  simp only [Nat.pow_succ,Nat.pow_zero] at *
  omega

theorem next_size (k : Nat) : 4*2^(2*(k+1))=2^(2*(k+2)) := by
  rw [show 2*(k+2)=2*(k+1)+2 by omega,Nat.pow_add]
  simp only [Nat.pow_succ,Nat.pow_zero]
  omega

/-- Actual Hamilton decomposition of every positive even-dimensional cube.
The induction adds two dimensions; no Hamilton-existence premise is used. -/
noncomputable def decomposition : (m : Nat)→(hm : 0<m)→
    DecompositionData (Vertex (2*m)) (@Adjacent (2*m)) m (2^(2*m)) (Nat.two_pow_pos _) 
  | 0,hm => False.elim (by omega)
  | 1,_ => by simpa using BaseHamilton.decomposition
  | k+2,_ => by
    let D := decomposition (k+1) (by omega)
    let selected := Classical.choose (even_cube_select_disjoint_edges D)
    have hn := Classical.choose_spec (even_cube_select_disjoint_edges D)
    let P := HamiltonPartition.product D selected hn (room_three k)
    let T := CubeHierarchy.transport (appendTwo (2*(k+1))) P
    exact castData (by omega) rfl (next_size k) T

/-- The same uniform result in the even-dimension form used by the target. -/
theorem exists_even (n : Nat) (hn : 2≤n) (he : 2∣n) :
    Nonempty (DecompositionData (Vertex n) (@Adjacent n) (n/2) (2^n) (Nat.two_pow_pos _)) := by
  obtain ⟨m,hm⟩ := he
  have hp : 0<m := by omega
  have hf : m=n/2 := by omega
  exact ⟨castData hm.symm hf (congrArg (fun q=>2^q) hm.symm) (decomposition m hp)⟩

#print axioms appendTwo
#print axioms decomposition
#print axioms exists_even
end ErdePaths.EvenHamilton
