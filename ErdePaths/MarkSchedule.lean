import ErdePaths.ChordColor
import ErdePaths.ChordSchedule

namespace ErdePaths.MarkSchedule
open ChordGraph ChordColor ChordSchedule

/-- Actual finite cube vertices, without a supplied finiteness oracle. -/
def cubeEnumeration (n : Nat) : Enumeration (Vertex n) where
  vertices := List.finRange (2^n)
  distinct := List.nodup_finRange _
  covers v := List.mem_finRange v

/-- The output of the PROVED coloring/grammar construction. The input marks
retain the separate physical balance/multiplicity geometry obligations. -/
structure Data {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) where
  labels : (i : Fin m) → Fin (M.word i).length → Fin b
  palette : ∀ v (c : Fin b), ((List.finRange m).map (fun i =>
    (List.finRange (M.word i).length).countP
      (fun o => decide ((M.word i)[o]=v ∧ labels i o=c)))).sum=1
  active : Fin m → Fin b
  inside : Fin m → NoncrossingWord.Forest (Fin b)
  outside : Fin m → NoncrossingWord.Forest (Fin b)
  order : ∀ i, (List.finRange (M.word i).length).map (labels i)=
    active i :: ((inside i).labels ++ active i :: (outside i).labels)
  passive : ∀ i, 1≤(inside i).pairCount+(outside i).pairCount

/-- Unconditional label-and-schedule existence from genuine balanced marks
and b-fold physical coverage. No label/coloring/schedule premise survives. -/
theorem exists_data {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (E : Enumeration V) (M : Marks V χ m b) (hlen : ∀ i, 4≤(M.word i).length) :
    Nonempty (Data M) := by
  classical
  obtain ⟨labels,hshared,hpalette⟩ := exists_palette_labels E M
  have hp (i : Fin m) : 2≤(M.forest i).pairCount := by
    have hh := (M.forest i).flatten_length
    rw [M.forest_flatten,List.length_finRange] at hh
    have := hlen i
    omega
  have hs (i : Fin m) : ∃ (a : Fin b) (inside outside : NoncrossingWord.Forest (Fin b)),
      (List.finRange (M.word i).length).map (labels i)=
        a::(inside.labels++a::outside.labels) ∧ 1≤inside.pairCount+outside.pairCount := by
    obtain ⟨a,inside,outside,he,hn⟩ := occurrence_schedule (labels i) (M.forest i) (hp i) (hshared i)
    rw [M.forest_flatten] at he
    exact ⟨a,inside,outside,he,hn⟩
  exact ⟨{
    labels := labels
    palette := hpalette
    active := fun i => Classical.choose (hs i)
    inside := fun i => Classical.choose (Classical.choose_spec (hs i))
    outside := fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (hs i)))
    order := fun i => (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hs i)))).1
    passive := fun i => (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hs i)))).2
  }⟩

/-- The common descriptor cycles appear in the literal original mark order,
including the closing endpoint of the active chord. No layers are reordered. -/
theorem descriptor_order {V X : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    {R : X → X → Prop} {ξ : X → Bool} {r : Nat} {hr : 0<r}
    {M : Marks V χ m b} (D : Data M)
    (cycles : Fin b → PairedLayers.CycleData X R ξ r hr) (i : Fin m) :
    (LayerPartition.descriptors (cycles (D.active i)) cycles (D.inside i) (D.outside i)).map Prod.fst =
      (List.finRange (M.word i).length).map (fun o => cycles (D.labels i o)) := by
  have hh := congrArg (List.map cycles) (D.order i)
  simp only [List.map_map,Function.comp_def,List.map_cons,List.map_append] at hh
  rw [hh]
  simp only [LayerPartition.descriptors,List.map_cons,List.map_append,List.map_map,Function.comp_def]

#print axioms exists_data
#print axioms descriptor_order
end ErdePaths.MarkSchedule
