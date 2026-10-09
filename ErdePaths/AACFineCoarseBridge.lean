import ErdePaths.SourceChronologicalMarks
import ErdePaths.AACIntervalSplit

namespace ErdePaths.AACFineCoarseBridge
open SquareLift AACTransition AACFine AACFineClock AACMerge

/-- A literal positive fine edge above every retained coarse edge label. -/
def liftLabel {K A B : Nat} (hA : 0<A) : CoarseEdge K B→FineEdge K A B
  | .inl (i,j) => .inl (AnchoredEmbedding.positionEncode i ⟨0,hA⟩,j)
  | .inr v => .inr v

theorem project_lift {K A B : Nat} (hA : 0<A) (e : CoarseEdge K B) :
    project (B:=B) hA (liftLabel hA e)=e := by
  cases e <;> simp [liftLabel,project,AnchoredEmbedding.positionDecode_encode]

/-- Fine-label ownership forces coarse-label ownership for the SAME actual
Euler clock. No second traversal or coarse-injection premise is substituted. -/
theorem coarse_injective {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A:=A) C).length=E)
    (hinj : Function.Injective (fineLabel hK hA hB C hE)) :
    Function.Injective (fun n=>AACEdge.incoming hK hB (C.point n)) := by
  intro i j hij
  let p := predecessor hN i
  let q := predecessor hN j
  let e := liftLabel (B:=B) hA (AACEdge.incoming hK hB (C.point i))
  have hp : project hA e=AACEdge.incoming hK hB (cross hK hB (atPair turns (C.point p))) := by
    change project hA e=AACEdge.incoming hK hB (transition hK hB turns (C.point p))
    rw [C.next]
    simp only [p,successor_predecessor,e,project_lift]
  have hq : project hA e=AACEdge.incoming hK hB (cross hK hB (atPair turns (C.point q))) := by
    change project hA e=AACEdge.incoming hK hB (transition hK hB turns (C.point q))
    rw [C.next]
    simpa only [q,successor_predecessor,e,project_lift] using hij
  obtain ⟨k,hk⟩ := segment_label_covers hK hA hB (atPair turns (C.point p)) e hp
  obtain ⟨l,hl⟩ := segment_label_covers hK hA hB (atPair turns (C.point q)) e hq
  let x : ExpandedIndex (A:=A) C := ⟨p,k⟩
  let y : ExpandedIndex (A:=A) C := ⟨q,l⟩
  have hx : fineLabel hK hA hB C hE (exactInverse C hE x)=e := by
    change expandedLabel hK hA hB C (exactPosition C hE (exactInverse C hE x))=e
    rw [exactPosition_inverse]
    exact hk
  have hy : fineLabel hK hA hB C hE (exactInverse C hE y)=e := by
    change expandedLabel hK hA hB C (exactPosition C hE (exactInverse C hE y))=e
    rw [exactPosition_inverse]
    exact hl
  have hn := hinj (hx.trans hy.symm)
  have hxy : x=y := by
    have hh := congrArg (exactPosition C hE) hn
    simpa only [exactPosition_inverse] using hh
  have hpq : p=q := congrArg Sigma.fst hxy
  simpa only [p,q,successor_predecessor] using congrArg (successor hN) hpq

/-- Actual geometric collision law for a constructed owned Euler word. -/
theorem euler_collision {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (t : Fin K→Bool) (D : SourceChronologicalMarks.EulerData hK hA hB t)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hbeven : B%2=0) (hE2 : 2≤K*B*(A+1))
    (z : Fin A) (hz : 0<z.val) (n m : Fin (K*B*(A+1)))
    (he : fineVertex hK hA hB D.orbit D.length n=fineVertex hK hA hB D.orbit D.length m) :
    n=m ∨ AACMarkIntervals.numericColor hK hA hB D.orbit D.length z n≠
      AACMarkIntervals.numericColor hK hA hB D.orbit D.length z m :=
  AACIntervalSplit.numeric_color_collision hK hA hB h3 hB3 hbeven D.orbit D.length
    (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) hE2 D.injective
    (coarse_injective hK hA hB D.orbit D.length D.injective) z hz n m he

#print axioms coarse_injective
#print axioms euler_collision
end ErdePaths.AACFineCoarseBridge
