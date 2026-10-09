import ErdePaths.Compatible
import ErdePaths.Subdivision
import ErdePaths.SquareLift

namespace ErdePaths.GraphTarget

theorem edge_iff {n L : Nat} (p : Fin (L+1) → Vertex n) (u v : Vertex n) :
    UsesEdge (List.ofFn p) u v ↔ ∃ j : Fin L,
      UndirectedEq (p j.castSucc,p j.succ) (u,v) := by
  rw [usesEdge_iff_position]
  constructor
  · rintro ⟨t,ht,he⟩
    have hj : t<L := by simp only [List.length_ofFn] at ht; omega
    refine ⟨⟨t,hj⟩,?_⟩
    simp only [List.getElem_ofFn] at he
    rcases he with he | he
    · exact Or.inl (Prod.ext he.1 he.2)
    · exact Or.inr (Prod.ext he.1 he.2)
  · rintro ⟨j,he⟩
    refine ⟨j.val,⟨by simp only [List.length_ofFn]; have := j.isLt; omega,?_⟩⟩
    simp only [List.getElem_ofFn]
    rcases he with he | he
    · left
      exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
    · right
      exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- Faithful conversion from checked finite indexed graph paths to the exact
list-based target proposition. No target existence premise is introduced. -/
theorem to_target {n L : Nat} (D : GraphPathDecomposition (Vertex n) (@Adjacent n) L) :
    HasPathDecomposition n L := by
  refine ⟨D.Index,D.indices,fun p => List.ofFn (D.vertices p),?_,?_⟩
  · intro p hp
    have hn : (List.ofFn (D.vertices p)).Nodup := by
      apply List.nodup_iff_eq_of_getElem_eq.mpr
      intro i j hi hj he
      simp only [List.getElem_ofFn] at he
      exact congrArg (fun x : Fin (L+1) => x.val) (D.simple p hp he)
    refine ⟨List.length_ofFn,hn,?_⟩
    intro e he
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp he
    have hbound : j<L := by
      simp only [steps,List.length_zip,List.length_tail,List.length_ofFn,Nat.add_sub_cancel] at hj
      omega
    have heq : e=(D.vertices p ⟨j,by omega⟩,D.vertices p ⟨j+1,by omega⟩) := by
      simpa only [steps,List.getElem_zip,List.getElem_tail,List.getElem_ofFn] using he.symm
    rw [heq]
    exact D.adjacent p hp ⟨j,hbound⟩
  · intro u v huv
    obtain ⟨p,hp,j,hj⟩ := D.cover u v huv
    refine ⟨p,hp,(edge_iff _ _ _).mpr ⟨j,hj⟩,?_⟩
    intro q hq hquv
    obtain ⟨k,hk⟩ := (edge_iff _ _ _).mp hquv
    have he : UndirectedEq (D.vertices q k.castSucc,D.vertices q k.succ)
        (D.vertices p j.castSucc,D.vertices p j.succ) :=
      SquareLift.sameEdge_trans hk (SquareLift.sameEdge_symm hj)
    exact (D.unique q p hq hp k j he).1

#print axioms to_target
end ErdePaths.GraphTarget
