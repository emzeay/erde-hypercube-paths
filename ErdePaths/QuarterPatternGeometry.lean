import ErdePaths.AACIsolatedFork
import ErdePaths.SourceChronologicalMarks
import ErdePaths.SourceAACBase

namespace ErdePaths.QuarterPatternGeometry
open SquareLift SourceClock AACTransition AACFine AACFineClock AACFineGeometry AACMarkIntervals
attribute [local instance] Classical.propDecidable

/-- Literal 0011 word, periodically repeated on the actual coarse cycle. -/
def quarter {K : Nat} : Fin K→Bool :=
  TurnPatterns.repeated (by decide : 0<4) (TurnPatterns.anti (L:=2) 1)

/-- Actual balanced-word chain merger and fine expansion; no Euler clock,
coverage or transition invariant is assumed. -/
noncomputable def euler {K B : Nat} (hK : 0<K) (hB : 0<B) (hd : 4∣K) :
    SourceChronologicalMarks.EulerData hK (by decide : 0<2) hB (quarter (K:=K)) :=
  SourceChronologicalMarks.euler hK (by decide) hB quarter
    (TurnPatterns.repeated_anti_balanced (by decide : 0<2) hd 1)
    ((TurnPatterns.repeated_zero _ _ _).trans (TurnPatterns.anti_zero (by decide : 0<2)))

/-- Flipping column zero in any nonlast row changes the literal local
quarter turns to 1,0,1 around column one. -/
theorem flipped_isolated {K B : Nat} (hK : 0<K) (_hB : 0<B) (hK4 : 4≤K)
    (j : Fin B) (hj : j.val<B-1) :
    let i : Fin K := ⟨1,by omega⟩
    let turns := AACInduction.turnsAfter hK (quarter (K:=K)) (B-1)
    turns (predecessor hK i,j)=true ∧ turns (i,j)=false ∧ turns (successor hK i,j)=true := by
  dsimp only
  have hp : predecessor hK (⟨1,by omega⟩ : Fin K)=⟨0,hK⟩ := by
    apply Fin.ext
    change (K-1+1)%K=0
    rw [show K-1+1=K by omega,Nat.mod_self]
  have hs : successor hK (⟨1,by omega⟩ : Fin K)=⟨2,by omega⟩ := by
    apply Fin.ext
    change (1+1)%K=2
    exact Nat.mod_eq_of_lt (by omega)
  have hn1 : (⟨1,by omega⟩ : Fin K)≠⟨0,hK⟩ := by intro he; have hh := congrArg Fin.val he; change 1=0 at hh; omega
  have hn2 : (⟨2,by omega⟩ : Fin K)≠⟨0,hK⟩ := by intro he; have hh := congrArg Fin.val he; change 2=0 at hh; omega
  rw [hp,hs]
  simp only [AACInduction.turnsAfter,hj,and_self,ite_true,hn1,hn2,false_and,ite_false,
    quarter,TurnPatterns.repeated]
  simp [TurnPatterns.anti,TurnPatterns.antiCore]

/-- Actual numeric fine Euler occurrences of both isolated internal
neighbors, with uniqueness, unmarked flags and opposite chronological colors.
All turn/occurrence/ownership facts are derived from the 0011 construction. -/
theorem numeric_neighbors {K B : Nat} (hK : 0<K) (hB : 0<B) (hd : 4∣K)
    (hB4 : 4≤B) (hb : B%2=0) (j : Fin B) (hj : j.val<B-1) :
    let E := euler hK hB hd
    let pos := Nat.mul_pos (Nat.mul_pos hK hB) (by decide : 0<2+1)
    let i : Fin K := ⟨1,by have := Nat.le_of_dvd hK hd; omega⟩
    let color := numericColor hK (by decide : 0<2) hB E.orbit E.length (⟨1,by decide⟩ : Fin 2)
    ∃n m : Fin (K*B*(2+1)),
      fineVertex hK (by decide : 0<2) hB E.orbit E.length n=
        (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),j) ∧
      fineVertex hK (by decide : 0<2) hB E.orbit E.length m=
        (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j) ∧
      (∀p,fineVertex hK (by decide : 0<2) hB E.orbit E.length p=
        fineVertex hK (by decide : 0<2) hB E.orbit E.length n→p=n) ∧
      (∀p,fineVertex hK (by decide : 0<2) hB E.orbit E.length p=
        fineVertex hK (by decide : 0<2) hB E.orbit E.length m→p=m) ∧
      cyclicFlag pos color n=false ∧ cyclicFlag pos color m=false ∧ color n≠color m := by
  dsimp only
  have hK4 : 4≤K := Nat.le_of_dvd hK hd
  have hi := flipped_isolated hK hB hK4 j hj
  have h3 : 3≤K*2 := by omega
  have hE2 : 2≤K*B*(2+1) := by
    have hh := Nat.mul_pos hK hB
    omega
  exact AACIsolatedFork.isolated_occurrences hK hB h3 (by omega) hb (euler hK hB hd).orbit
    (euler hK hB hd).length (Nat.mul_pos (Nat.mul_pos hK hB) (by decide)) hE2
    (euler hK hB hd).injective (euler hK hB hd).surjective ⟨1,by omega⟩ j
    (by rw [hi.1,hi.2.1]; decide) (by rw [hi.2.1,hi.2.2]; decide)

/-- The same derived witnesses in arbitrary genuine Hamilton coordinates.
Neither physical neighbor existence nor exclusivity is assumed. -/
theorem physical_neighbors {K B : Nat} {U W : Type} (hK : 0<K) (hB : 0<B) (hd : 4∣K)
    (hB4 : 4≤B) (hb : B%2=0) (G : ClockData U (K*2)) (H : ClockData W B)
    (j : Fin B) (hj : j.val<B-1) :
    let E := euler hK hB hd
    let pos := Nat.mul_pos (Nat.mul_pos hK hB) (by decide : 0<2+1)
    let i : Fin K := ⟨1,by have := Nat.le_of_dvd hK hd; omega⟩
    let base := SourceAACBase.base hK (by decide : 0<2) hB E G H
    let color := numericColor hK (by decide : 0<2) hB E.orbit E.length (⟨1,by decide⟩ : Fin 2)
    ∃n m : Fin (K*B*(2+1)),
      base n=physical G H (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),j) ∧
      base m=physical G H (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j) ∧
      (∀p,base p=base n→p=n) ∧ (∀p,base p=base m→p=m) ∧
      cyclicFlag pos color n=false ∧ cyclicFlag pos color m=false ∧ color n≠color m := by
  dsimp only
  obtain ⟨n,m,hn,hm,hnu,hmu,hnf,hmf,hc⟩ := numeric_neighbors hK hB hd hB4 hb j hj
  refine ⟨n,m,congrArg (physical G H) hn,congrArg (physical G H) hm,?_,?_,hnf,hmf,hc⟩
  · intro p hp
    exact hnu p (physical_injective G H hp)
  · intro p hp
    exact hmu p (physical_injective G H hp)

/-- Row zero is always a genuinely flipped row under the actual B-1 chain
merger for B>=4. This supplies a canonical row without an extra row premise. -/
theorem zero_row_neighbors {K B : Nat} {U W : Type} (hK : 0<K) (hB : 0<B) (hd : 4∣K)
    (hB4 : 4≤B) (hb : B%2=0) (G : ClockData U (K*2)) (H : ClockData W B) :
    let E := euler hK hB hd
    let pos := Nat.mul_pos (Nat.mul_pos hK hB) (by decide : 0<2+1)
    let i : Fin K := ⟨1,by have := Nat.le_of_dvd hK hd; omega⟩
    let base := SourceAACBase.base hK (by decide : 0<2) hB E G H
    let color := numericColor hK (by decide : 0<2) hB E.orbit E.length (⟨1,by decide⟩ : Fin 2)
    ∃n m : Fin (K*B*(2+1)),
      base n=physical G H (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),⟨0,hB⟩) ∧
      base m=physical G H (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),⟨0,hB⟩) ∧
      (∀p,base p=base n→p=n) ∧ (∀p,base p=base m→p=m) ∧
      cyclicFlag pos color n=false ∧ cyclicFlag pos color m=false ∧ color n≠color m :=
  physical_neighbors hK hB hd hB4 hb G H ⟨0,hB⟩ (by change 0<B-1; omega)

#print axioms zero_row_neighbors
#print axioms physical_neighbors
#print axioms euler
#print axioms flipped_isolated
#print axioms numeric_neighbors
end ErdePaths.QuarterPatternGeometry
