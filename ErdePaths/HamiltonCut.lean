import ErdePaths.HamiltonData
import ErdePaths.GraphTarget

namespace ErdePaths.HamiltonCut
open HamiltonData SquareLift

variable {V : Type} {R : V → V → Prop} {m N L : Nat} {hN : 0<N}

def phase (hL : 0<L) (hdiv : L∣N) (p : Fin (N/L)) : Fin N :=
  ⟨p.val*L,by
    have hp := p.isLt
    have he : N/L*L=N := Nat.div_mul_cancel hdiv
    have hm := Nat.mul_lt_mul_of_pos_right hp hL
    omega⟩

def vertex (D : DecompositionData V R m N hN) (hL : 0<L) (hLN : L<N)
    (hdiv : L∣N) (p : Fin m × Fin (N/L)) (j : Fin (L+1)) : V :=
  (D.cycles p.1).cycle (forward hN (phase hL hdiv p.2) ⟨j.val,by have := j.isLt; omega⟩)

theorem simple (D : DecompositionData V R m N hN) (hL : 0<L) (hLN : L<N)
    (hdiv : L∣N) (p : Fin m × Fin (N/L)) : Function.Injective (vertex D hL hLN hdiv p) := by
  intro i j hh
  have hf := forward_injective hN (phase hL hdiv p.2) (cycle_injective (D.cycles p.1) hh)
  exact Fin.ext (congrArg (fun x : Fin N => x.val) hf)

def stepPhase (_hL : 0<L) (hdiv : L∣N) (p : Fin (N/L)) (j : Fin L) : Fin N :=
  ⟨p.val*L+j.val,by
    have hp := p.isLt
    have hj := j.isLt
    have he : N/L*L=N := Nat.div_mul_cancel hdiv
    have hm := Nat.mul_le_mul_right L (show p.val+1≤N/L by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hm
    omega⟩

theorem source (D : DecompositionData V R m N hN) (hL : 0<L) (hLN : L<N)
    (hdiv : L∣N) (p : Fin m × Fin (N/L)) (j : Fin L) :
    vertex D hL hLN hdiv p j.castSucc=(D.cycles p.1).cycle (stepPhase hL hdiv p.2 j) := by
  unfold vertex
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (stepPhase hL hdiv p.2 j).isLt

theorem target (D : DecompositionData V R m N hN) (hL : 0<L) (hLN : L<N)
    (hdiv : L∣N) (p : Fin m × Fin (N/L)) (j : Fin L) :
    vertex D hL hLN hdiv p j.succ=
      (D.cycles p.1).cycle (successor hN (stepPhase hL hdiv p.2 j)) := by
  unfold vertex
  congr 1

theorem positions_cover (hL : 0<L) (hdiv : L∣N) (t : Fin N) :
    ∃ p j, stepPhase hL hdiv p j=t := by
  have he : N/L*L=N := Nat.div_mul_cancel hdiv
  have hp : t.val/L<N/L := by
    by_cases hh : t.val/L<N/L
    · exact hh
    ·
      have hm := Nat.mul_le_mul_right L (show N/L≤t.val/L by omega)
      have hd := Nat.div_mul_le_self t.val L
      have ht := t.isLt
      omega
  refine ⟨⟨t.val/L,hp⟩,⟨t.val%L,Nat.mod_lt _ hL⟩,?_⟩
  apply Fin.ext
  simpa only [stepPhase,Fin.val_mk,Nat.mul_comm] using Nat.div_add_mod t.val L

theorem positions_unique (hL : 0<L) (hdiv : L∣N)
    (p q : Fin (N/L)) (j k : Fin L) (he : stepPhase hL hdiv p j=stepPhase hL hdiv q k) :
    p=q ∧ j=k := by
  have hv := congrArg (fun x : Fin N => x.val) he
  have hj := j.isLt
  have hk := k.isLt
  simp only [stepPhase,Fin.val_mk] at hv
  have hp : p.val=q.val := by
    have hm := congrArg (fun x => x/L) hv
    rw [Nat.mul_comm p.val L,Nat.mul_comm q.val L,Nat.mul_add_div hL,Nat.mul_add_div hL,
      Nat.div_eq_of_lt hj,Nat.div_eq_of_lt hk,Nat.add_zero,Nat.add_zero] at hm
    exact hm
  rw [hp] at hv
  exact ⟨Fin.ext hp,Fin.ext (by omega)⟩

noncomputable def decomposition (D : DecompositionData V R m N hN)
    (hL : 0<L) (hLN : L<N) (hdiv : L∣N) : GraphPathDecomposition V R L where
  Index := Fin m × Fin (N/L)
  indices := (List.finRange m).flatMap (fun f => (List.finRange (N/L)).map (fun p => (f,p)))
  vertices := vertex D hL hLN hdiv
  simple p _ := simple D hL hLN hdiv p
  adjacent p _ j := by
    rw [source,target]
    exact (D.cycles p.1).adjacent _
  cover u v huv := by
    obtain ⟨f,t,ht⟩ := D.cover u v huv
    obtain ⟨p,j,hp⟩ := positions_cover hL hdiv t
    refine ⟨(f,p),by simp,j,?_⟩
    rw [source,target,hp]
    exact ht
  unique p q _ _ j k he := by
    rw [source,target,source,target] at he
    have hh := D.unique _ _ _ _ he
    have hp := positions_unique hL hdiv p.2 q.2 j k hh.2
    exact ⟨Prod.ext hh.1 hp.1,hp.2⟩

/-- Actual cube Hamilton factors supply every proper divisor of their length.
This consumes displayed factors; it does not assert their existence. -/
theorem cube_cut {n m L : Nat}
    (D : DecompositionData (ErdePaths.Vertex n) (@ErdePaths.Adjacent n) m (2^n) (Nat.two_pow_pos n))
    (hL : 0<L) (hLN : L<2^n) (hdiv : L∣2^n) : HasPathDecomposition n L :=
  GraphTarget.to_target (decomposition D hL hLN hdiv)

#print axioms cube_cut
#print axioms decomposition
end ErdePaths.HamiltonCut
