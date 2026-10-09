import ErdePaths.HamiltonData

namespace ErdePaths.FiniteSaturation

/-- Coverage follows from proved injection and the exact size of an explicit
finite carrier. The carrier need not itself be assumed Nodup. -/
theorem list_full {α : Type} {items carrier : List α}
    (hi : items.Nodup) (hsub : items ⊆ carrier)
    (hlen : carrier.length ≤ items.length) : carrier ⊆ items := by
  intro v hv
  by_cases hm : v ∈ items
  · exact hm
  · have hn : (v :: items).Nodup := List.nodup_cons.mpr ⟨hm,hi⟩
    have hs : v :: items ⊆ carrier := by
      intro w hw
      rcases List.mem_cons.mp hw with he | hw
      · exact he ▸ hv
      · exact hsub hw
    have hc := hn.length_le_of_subset hs
    simp only [List.length_cons] at hc
    omega

theorem ofFn_nodup {α : Type} {N : Nat} (f : Fin N → α)
    (hinj : ∀ i j, f i = f j → i=j) : (List.ofFn f).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  simp only [List.getElem_ofFn] at he
  exact congrArg Fin.val (hinj _ _ he)

theorem fin_surjective {N : Nat} (f : Fin N → Fin N)
    (hinj : ∀ i j, f i=f j → i=j) : ∀ v, ∃ i, f i=v := by
  intro v
  have hs : List.ofFn f ⊆ List.finRange N := by
    intro w _
    exact List.mem_finRange w
  have hc := list_full (ofFn_nodup f hinj) hs
    (by simp only [List.length_finRange,List.length_ofFn]; omega)
  exact List.mem_ofFn.mp (hc (List.mem_finRange v))

#print axioms list_full
#print axioms fin_surjective
end ErdePaths.FiniteSaturation
