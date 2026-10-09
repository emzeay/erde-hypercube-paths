import ErdePaths.SourceFork

namespace ErdePaths.AACIsolatedFork
open SquareLift AACTransition AACFine AACFineClock AACFineGeometry AACMarkIntervals
attribute [local instance] Classical.propDecidable

/-- On an unmarked A=2 subdivided edge, the ACTUAL outgoing Euler color at
its unique internal vertex is the common endpoint color, in either direction. -/
theorem internal_color {K B N E : Nat} (hK : 0<K) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (O : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A:=2) O).length=E) (hpos : 0<E)
    (i : Fin K) (j : Fin B) (n : Fin E)
    (hn : fineVertex hK (by decide : 0<2) hB O hE n=
      (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j))
    (ht : turns (i,j)≠turns (successor hK i,j)) :
    numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2) n=startColor turns i j := by
  have hp : predecessor (Nat.mul_pos hK (by decide : 0<2))
      (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2))=
      AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2) := by
    have hs : successor (Nat.mul_pos hK (by decide : 0<2))
        (AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2))=
        AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2) := by
      apply Fin.ext
      simp only [successor,AnchoredEmbedding.positionEncode,Nat.add_zero]
      have hi := i.isLt
      have hm := Nat.mul_le_mul_left 2 (show i.val+1≤K by omega)
      simp only [Nat.mul_add,Nat.mul_one] at hm
      exact Nat.mod_eq_of_lt (by omega)
    have hh := congrArg (predecessor (Nat.mul_pos hK (by decide : 0<2))) hs
    rw [predecessor_successor] at hh
    exact hh.symm
  have hv : NonGrid (by decide : 0<2) (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j) := by
    apply (nonGrid_iff (by decide : 0<2) _).mpr
    simp only [AnchoredEmbedding.positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt (show 1<2 by decide)]
    decide
  have he := fineVertex_step hK (by decide : 0<2) hB O hE hpos n
  rw [hn] at he
  unfold numericColor
  cases hf : fineLabel hK (by decide : 0<2) hB O hE n with
  | inl p =>
    rcases p with ⟨x,row⟩
    rw [hf] at he
    rcases he with he|he
    · have hx : x=AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2) := congrArg (fun e=>e.1.1) he
      have hj : row=j := congrArg (fun e=>e.1.2) he
      subst x; subst row
      rw [edgeColor_after hK (by decide : 0<2) turns
        (⟨1,by decide⟩ : Fin 2) (⟨1,by decide⟩ : Fin 2) i j (by decide)]
      have hc : startColor turns i j=endColor hK turns i j := by
        by_cases hc : startColor turns i j=endColor hK turns i j
        · exact hc
        · exact False.elim (ht ((endpoint_change_iff hK turns i j).mp hc))
      exact hc.symm
    · have hx : successor (Nat.mul_pos hK (by decide : 0<2)) x=
          AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2) := congrArg (fun e=>e.2.1) he
      have hj : row=j := congrArg (fun e=>e.2.2) he
      have hx' : x=AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2) := by
        have hh := congrArg (predecessor (Nat.mul_pos hK (by decide : 0<2))) hx
        rw [predecessor_successor,hp] at hh
        exact hh
      subst x; subst row
      exact edgeColor_before hK (by decide : 0<2) turns
        (⟨1,by decide⟩ : Fin 2) (⟨0,by decide⟩ : Fin 2) i j (by decide)
  | inr p =>
    rcases p with ⟨x,row⟩
    rw [hf] at he
    rcases he with he|he
    · exact False.elim (hv (x,row) (congrArg Prod.fst he).symm)
    · exact False.elim (hv (x,successor hB row) (congrArg Prod.snd he).symm)

/-- Literal internal neighbors at an isolated turn have opposite ACTUAL
chronological Euler colors, regardless of the directions of either visit. -/
theorem isolated_colors {K B N E : Nat} (hK : 0<K) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (O : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A:=2) O).length=E) (hpos : 0<E)
    (i : Fin K) (j : Fin B) (n m : Fin E)
    (hn : fineVertex hK (by decide : 0<2) hB O hE n=
      (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),j))
    (hm : fineVertex hK (by decide : 0<2) hB O hE m=
      (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j))
    (hbefore : turns (predecessor hK i,j)≠turns (i,j))
    (hafter : turns (i,j)≠turns (successor hK i,j)) :
    numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2) n≠
      numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2) m := by
  have hb : turns (predecessor hK i,j)≠turns (successor hK (predecessor hK i),j) := by
    simpa only [successor_predecessor] using hbefore
  rw [internal_color hK hB O hE hpos (predecessor hK i) j n hn hb,
    internal_color hK hB O hE hpos i j m hm hafter]
  unfold startColor
  cases hr : rowColor j <;> cases ht : turns (predecessor hK i,j) <;> cases hu : turns (i,j) <;>
    simp_all

/-- Existence, uniqueness, unmarked flags and opposite colors of both
literal isolated-turn neighbors are derived from actual Euler edge labels. -/
theorem isolated_occurrences {K B N E : Nat} (hK : 0<K) (hB : 0<B)
    (h3 : 3≤K*2) (hB3 : 3≤B) (hb : B%2=0)
    {hN : 0<N} {turns : Grid K B→Bool}
    (O : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A:=2) O).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel hK (by decide : 0<2) hB O hE))
    (hsur : Function.Surjective (fineLabel hK (by decide : 0<2) hB O hE))
    (i : Fin K) (j : Fin B)
    (hbefore : turns (predecessor hK i,j)≠turns (i,j))
    (hafter : turns (i,j)≠turns (successor hK i,j)) :
    ∃n m : Fin E,
      fineVertex hK (by decide : 0<2) hB O hE n=
        (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),j) ∧
      fineVertex hK (by decide : 0<2) hB O hE m=
        (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j) ∧
      (∀p,fineVertex hK (by decide : 0<2) hB O hE p=fineVertex hK (by decide : 0<2) hB O hE n→p=n) ∧
      (∀p,fineVertex hK (by decide : 0<2) hB O hE p=fineVertex hK (by decide : 0<2) hB O hE m→p=m) ∧
      cyclicFlag hpos (numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2)) n=false ∧
      cyclicFlag hpos (numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2)) m=false ∧
      numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2) n≠
        numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2) m := by
  obtain ⟨n,hn,hnu⟩ := internal_clock_owner hK (by decide : 0<2) hB h3 hB3 O hE hpos hE2 hinj hsur
    (predecessor hK i) (⟨1,by decide⟩ : Fin 2) (by decide) j
  obtain ⟨m,hm,hmu⟩ := internal_clock_owner hK (by decide : 0<2) hB h3 hB3 O hE hpos hE2 hinj hsur
    i (⟨1,by decide⟩ : Fin 2) (by decide) j
  have hc := isolated_colors hK hB O hE hpos i j n m hn hm hbefore hafter
  have hmarks := AACFoldFork.isolated_two_neighbors hK turns i j hbefore hafter
  have hnf : cyclicFlag hpos (numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2)) n=false := by
    cases hf : cyclicFlag hpos (numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2)) n
    · rfl
    · have hh := (AACFoldFork.actual_flag_iff hK (by decide : 0<2) hB hb O hE hpos
        (⟨1,by decide⟩ : Fin 2) (by decide) n).mp hf
      rw [hn] at hh
      exact False.elim (hmarks.1 hh)
  have hmf : cyclicFlag hpos (numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2)) m=false := by
    cases hf : cyclicFlag hpos (numericColor hK (by decide : 0<2) hB O hE (⟨1,by decide⟩ : Fin 2)) m
    · rfl
    · have hh := (AACFoldFork.actual_flag_iff hK (by decide : 0<2) hB hb O hE hpos
        (⟨1,by decide⟩ : Fin 2) (by decide) m).mp hf
      rw [hm] at hh
      exact False.elim (hmarks.2.1 hh)
  exact ⟨n,m,hn,hm,(fun p hp=>hnu p (hp.trans hn)),(fun p hp=>hmu p (hp.trans hm)),hnf,hmf,hc⟩

#print axioms isolated_colors
#print axioms isolated_occurrences
#print axioms internal_color
end ErdePaths.AACIsolatedFork
