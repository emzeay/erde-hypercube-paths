import ErdePaths.CubeParity
import ErdePaths.HamiltonNormalize

namespace ErdePaths.CubeCycle
open SquareLift CubeParity

/-- Actual cyclic positions of the two physical bipartition sides. -/
def index {r : Nat} (_hr : 0<r) (p : Fin r×Bool) : Fin (2*r) :=
  ⟨2*p.1.val+(if p.2 then 1 else 0),by have := p.1.isLt; cases p.2 <;> simp <;> omega⟩

def coordinates {r : Nat} (_hr : 0<r) (t : Fin (2*r)) : Fin r×Bool :=
  (⟨t.val/2,by have := t.isLt; omega⟩,decide (t.val%2=1))

theorem coordinates_index {r : Nat} (hr : 0<r) (p : Fin r×Bool) :
    coordinates hr (index hr p)=p := by
  apply Prod.ext
  · apply Fin.ext
    cases hp : p.2 <;> simp [coordinates,index,hp] <;> omega
  · cases hp : p.2 <;> simp [coordinates,index,hp] <;> omega

theorem index_coordinates {r : Nat} (hr : 0<r) (t : Fin (2*r)) :
    index hr (coordinates hr t)=t := by
  apply Fin.ext
  have hm : t.val%2<2 := Nat.mod_lt t.val (by decide)
  simp only [index,coordinates]
  by_cases hh : t.val%2=1 <;> simp [hh] <;> omega

theorem index_even_next {r : Nat} (hr : 0<r) (t : Fin r) :
    successor (by omega : 0<2*r) (index hr (t,false))=index hr (t,true) := by
  apply Fin.ext
  have ht : 2*t.val+1<2*r := by have := t.isLt; omega
  simp only [successor,index,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
  exact Nat.mod_eq_of_lt ht

theorem index_odd_next {r : Nat} (hr : 0<r) (t : Fin r) :
    successor (by omega : 0<2*r) (index hr (t,true))=index hr (successor hr t,false) := by
  apply Fin.ext
  simp only [successor,index,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
  have ht := t.isLt
  by_cases hh : t.val+1<r
  · have hh' : 2*t.val+1+1<2*r := by omega
    rw [Nat.mod_eq_of_lt hh,Nat.mod_eq_of_lt hh']
    omega
  · have he : t.val+1=r := by omega
    have he' : 2*t.val+1+1=2*r := by omega
    rw [he,he',Nat.mod_self,Nat.mod_self,Nat.mul_zero]

/-- Convert actual numeric cube Hamilton data to the physical bipartite
clock needed by multilabel folding. Origin phase is explicitly verified. -/
def paired {n r : Nat} (hr : 0<r)
    (C : HamiltonData.CycleData (Vertex n) (@Adjacent n) (2*r) (by omega))
    (horigin : parity (C.cycle ⟨0,by omega⟩)=false) :
    PairedLayers.CycleData (Vertex n) (@Adjacent n) parity r hr where
  vertex p := C.cycle (index hr p)
  coordinate v := coordinates hr (C.position v)
  coordinate_vertex p := by rw [C.position_cycle,coordinates_index]
  vertex_coordinate v := by rw [index_coordinates,C.cycle_position]
  bipartition t b := by
    rw [clock_parity (by omega) C,horigin,AACUnfold.flipN_mod]
    change (if (2*t.val+(if b then 1 else 0))%2=0 then false else true)=b
    cases b <;> simp <;> omega
  edge_even t := by
    have he := C.adjacent (index hr (t,false))
    rw [index_even_next] at he
    exact he
  edge_odd t := by
    have he := C.adjacent (index hr (t,true))
    rw [index_odd_next] at he
    exact he

/-- The actual all-zero cube vertex gives a uniformly valid clock phase;
there is no supplied abstract coloring or parity-origin assumption. -/
def atZero {n N : Nat} (hN : 0<N)
    (C : HamiltonData.CycleData (Vertex n) (@Adjacent n) N hN) :
    HamiltonData.CycleData (Vertex n) (@Adjacent n) N hN :=
  HamiltonNormalize.rotate C (C.position ⟨0,Nat.two_pow_pos n⟩)

theorem atZero_origin {n N : Nat} (hN : 0<N)
    (C : HamiltonData.CycleData (Vertex n) (@Adjacent n) N hN) :
    parity ((atZero hN C).cycle ⟨0,hN⟩)=false := by
  simp only [atZero,HamiltonNormalize.rotate,forward_zero,C.cycle_position]
  exact zero_parity n

def pairedCube {n r : Nat} (hr : 0<r)
    (C : HamiltonData.CycleData (Vertex n) (@Adjacent n) (2*r) (by omega)) :
    PairedLayers.CycleData (Vertex n) (@Adjacent n) parity r hr :=
  paired hr (atZero (by omega) C) (atZero_origin (by omega) C)

#print axioms pairedCube
#print axioms index_odd_next
end ErdePaths.CubeCycle
