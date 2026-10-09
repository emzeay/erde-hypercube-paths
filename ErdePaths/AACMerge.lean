import ErdePaths.AACTransition
import ErdePaths.HamiltonNormalize

namespace ErdePaths.AACMerge
open SquareLift AACTransition

/-- An actual cyclic orbit in a possibly larger state space. Surjectivity onto
all states and existence of a larger Euler orbit are not assumed. -/
structure Orbit (X : Type) (T : X → X) (N : Nat) (hN : 0<N) where
  point : Fin N → X
  injective : Function.Injective point
  next : ∀ i, T (point i)=point (successor hN i)

/-- Swap two actual state identities, retaining all other states. -/
def swapAt {X : Type} [DecidableEq X] (a b x : X) : X :=
  if x=a then b else if x=b then a else x

theorem swapAt_involutive {X : Type} [DecidableEq X] (a b x : X) :
    swapAt a b (swapAt a b x)=x := by
  by_cases hab : a=b
  · subst b; by_cases hx : x=a <;> simp [swapAt,hx]
  · by_cases hxa : x=a
    · subst x; simp [swapAt,Ne.symm hab]
    · by_cases hxb : x=b
      · subst x; simp [swapAt,Ne.symm hab]
      · simp [swapAt,hxa,hxb]

def splice {X : Type} [DecidableEq X] (T : X → X) (a b : X) : X → X :=
  fun x => T (swapAt a b x)

/-- The actual concatenated orbit clock after swapping its two closing steps. -/
def joined {X : Type} {T : X → X} {M N : Nat} {hM : 0<M} {hN : 0<N}
    (C : Orbit X T M hM) (D : Orbit X T N hN) (i : Fin (M+N)) : X :=
  if h : i.val<M then C.point ⟨i.val,h⟩ else D.point ⟨i.val-M,by have := i.isLt; omega⟩

theorem joined_injective {X : Type} {T : X → X} {M N : Nat} {hM : 0<M} {hN : 0<N}
    (C : Orbit X T M hM) (D : Orbit X T N hN)
    (hd : ∀ i j, C.point i ≠ D.point j) : Function.Injective (joined C D) := by
  intro i j h
  unfold joined at h
  split at h <;> split at h
  · have hv := congrArg (fun z : Fin M => z.val) (C.injective h)
    exact Fin.ext hv
  · exact False.elim (hd _ _ h)
  · exact False.elim (hd _ _ h.symm)
  · have hh := congrArg (fun z : Fin N => z.val) (D.injective h)
    change i.val-M=j.val-M at hh
    apply Fin.ext
    omega


def lastIndex {N : Nat} (hN : 0<N) : Fin N := ⟨N-1,by omega⟩

theorem Orbit.close {X : Type} {T : X → X} {N : Nat} {hN : 0<N} (C : Orbit X T N hN) :
    T (C.point (lastIndex hN))=C.point ⟨0,hN⟩ := by
  rw [C.next]
  congr 1
  apply Fin.ext
  simp only [successor,lastIndex]
  have hn : N-1+1=N := by omega
  rw [hn,Nat.mod_self]

/-- Splicing two disjoint actual directed circuits at their closing states
produces the actual concatenated circuit, with no existence oracle. -/
theorem joined_next {X : Type} [DecidableEq X] {T : X → X} {M N : Nat}
    {hM : 0<M} {hN : 0<N} (C : Orbit X T M hM) (D : Orbit X T N hN)
    (hd : ∀ i j, C.point i ≠ D.point j) (i : Fin (M+N)) :
    splice T (C.point (lastIndex hM)) (D.point (lastIndex hN)) (joined C D i)=
      joined C D (successor (by omega) i) := by
  have hiBound := i.isLt
  by_cases hi : i.val<M
  · by_cases hn : i.val+1<M
    · have hs : successor (by omega : 0<M+N) i=⟨i.val+1,by omega⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      have ha : C.point ⟨i.val,hi⟩ ≠ C.point (lastIndex hM) := by
        intro h
        have hv := congrArg (fun z : Fin M => z.val) (C.injective h)
        change i.val=M-1 at hv
        omega
      have hb := hd ⟨i.val,hi⟩ (lastIndex hN)
      simp only [hs,joined,dite_eq_left hi,dite_eq_left hn,splice,swapAt,ite_eq_right ha,ite_eq_right hb]
      rw [C.next]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hn)
    · have he : i.val+1=M := by omega
      have hs : successor (by omega : 0<M+N) i=⟨M,by omega⟩ := by
        apply Fin.ext
        simp only [successor,he,Nat.mod_eq_of_lt (show M<M+N by omega)]
      have hl : (⟨i.val,hi⟩ : Fin M)=lastIndex hM := Fin.ext (by simp only [lastIndex]; omega)
      simp only [hs,joined,dite_eq_left hi,dite_eq_right (Nat.lt_irrefl M),hl,splice,swapAt,↓reduceIte]
      simpa only [Nat.sub_self] using D.close
  · by_cases hn : i.val+1<M+N
    · have hs : successor (by omega : 0<M+N) i=⟨i.val+1,hn⟩ := Fin.ext (Nat.mod_eq_of_lt hn)
      have hnot : ¬i.val+1<M := by omega
      have ha : D.point ⟨i.val-M,by omega⟩ ≠ C.point (lastIndex hM) :=
        Ne.symm (hd (lastIndex hM) _)
      have hb : D.point ⟨i.val-M,by omega⟩ ≠ D.point (lastIndex hN) := by
        intro h
        have hv := congrArg (fun z : Fin N => z.val) (D.injective h)
        change i.val-M=N-1 at hv
        omega
      simp only [hs,joined,dite_eq_right hi,dite_eq_right hnot,splice,swapAt,ite_eq_right ha,ite_eq_right hb]
      rw [D.next]
      congr 1
      apply Fin.ext
      simp only [successor]
      rw [Nat.mod_eq_of_lt (show i.val-M+1<N by omega)]
      omega
    · have he : i.val+1=M+N := by omega
      have hs : successor (by omega : 0<M+N) i=⟨0,by omega⟩ := by
        apply Fin.ext
        simp only [successor,he,Nat.mod_self]
      have hl : (⟨i.val-M,by omega⟩ : Fin N)=lastIndex hN := Fin.ext (by simp only [lastIndex]; omega)
      have ha : D.point (lastIndex hN) ≠ C.point (lastIndex hM) := Ne.symm (hd _ _)
      simp only [hs,joined,dite_eq_right hi,dite_eq_left hM,hl,splice,swapAt,ite_eq_right ha,↓reduceIte]
      exact C.close


def joinedOrbit {X : Type} [DecidableEq X] {T : X → X} {M N : Nat}
    {hM : 0<M} {hN : 0<N} (C : Orbit X T M hM) (D : Orbit X T N hN)
    (hd : ∀ i j, C.point i ≠ D.point j) :
    Orbit X (splice T (C.point (lastIndex hM)) (D.point (lastIndex hN))) (M+N) (by omega) where
  point := joined C D
  injective := joined_injective C D hd
  next := joined_next C D hd

theorem joined_image {X : Type} {T : X → X} {M N : Nat} {hM : 0<M} {hN : 0<N}
    (C : Orbit X T M hM) (D : Orbit X T N hN) (x : X) :
    (∃ i, joined C D i=x) ↔ (∃ i, C.point i=x) ∨ (∃ j, D.point j=x) := by
  constructor
  · rintro ⟨i,hi⟩
    unfold joined at hi
    split at hi
    · exact Or.inl ⟨_,hi⟩
    · exact Or.inr ⟨_,hi⟩
  · rintro (⟨i,hi⟩ | ⟨j,hj⟩)
    · refine ⟨⟨i.val,by have := i.isLt; omega⟩,?_⟩
      simpa only [joined,dite_eq_left i.isLt] using hi
    · have hlt : M+j.val<M+N := by have := j.isLt; omega
      have hnot : ¬M+j.val<M := by omega
      refine ⟨⟨M+j.val,hlt⟩,?_⟩
      simpa only [joined,dite_eq_right hnot,Nat.add_sub_cancel_left] using hj

/-- The concrete AAC local flip, at an actual physical grid identity. -/
def flippedTurns {K B : Nat} (turns : Grid K B → Bool) (g : Grid K B) : Grid K B → Bool :=
  fun v => if v=g then !turns v else turns v

/-- A physical turn flip consists of two disjoint directed successor swaps.
This is why one must track a circuit and its reverse together. -/
theorem flip_transition {K B : Nat} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B → Bool) (g : Grid K B) (s : State K B) :
    transition hK hB (flippedTurns turns g) s =
      transition hK hB turns
        (swapAt (g.1,g.2,Port.up) (g.1,g.2,Port.down)
          (swapAt (g.1,g.2,Port.left) (g.1,g.2,Port.right) s)) := by
  by_cases hs : (s.1,s.2.1)=g
  · subst g
    rcases s with ⟨i,j,p⟩
    cases ht : turns (i,j) <;> cases p <;>
      simp [transition,atPair,flippedTurns,pair,swapAt,ht]
  · have hn (p : Port) : s≠(g.1,g.2,p) := by
      intro he
      have hh := congrArg (fun z : State K B => (z.1,z.2.1)) he
      exact hs hh
    simp only [swapAt,ite_eq_right (hn Port.left),ite_eq_right (hn Port.right),
      ite_eq_right (hn Port.up),ite_eq_right (hn Port.down)]
    simp [transition,atPair,flippedTurns,hs]

/-- Recenter an actual orbit at any chosen closing state. -/
def closeAt {X : Type} {T : X → X} {N : Nat} {hN : 0<N}
    (C : Orbit X T N hN) (cut : Fin N) : Orbit X T N hN where
  point i := C.point (forward hN (successor hN cut) i)
  injective := fun _ _ h => forward_injective hN _ (C.injective h)
  next i := by rw [C.next,←HamiltonNormalize.forward_successor]

theorem closeAt_last {X : Type} {T : X → X} {N : Nat} {hN : 0<N}
    (C : Orbit X T N hN) (cut : Fin N) : (closeAt C cut).point (lastIndex hN)=C.point cut := by
  simp only [closeAt,lastIndex,forward_last,predecessor_successor]

/-- A successor splice changes no actual orbit that misses its two cut states. -/
def Orbit.outside_splice {X : Type} [DecidableEq X] {T : X → X} {N : Nat} {hN : 0<N}
    (C : Orbit X T N hN) (a b : X) (ha : ∀ i, C.point i≠a) (hb : ∀ i, C.point i≠b) :
    Orbit X (splice T a b) N hN where
  point := C.point
  injective := C.injective
  next i := by simpa only [splice,swapAt,ite_eq_right (ha i),ite_eq_right (hb i)] using C.next i

theorem joined_avoids {X : Type} {T : X → X} {M N : Nat} {hM : 0<M} {hN : 0<N}
    (C : Orbit X T M hM) (D : Orbit X T N hN) (x : X)
    (hc : ∀ i, C.point i≠x) (hd : ∀ j, D.point j≠x) (i : Fin (M+N)) :
    joined C D i≠x := by
  intro he
  rcases (joined_image C D x).mp ⟨i,he⟩ with ⟨j,hj⟩ | ⟨j,hj⟩
  · exact hc j hj
  · exact hd j hj

/-- Two independent directed splices are the two orientations of a physical
circuit merger once the concrete port/reversal assignments are instantiated. -/
def doubleSplice {X : Type} [DecidableEq X] {T : X → X} {M N P Q : Nat}
    {hM : 0<M} {hN : 0<N} {hP : 0<P} {hQ : 0<Q}
    (C : Orbit X T M hM) (D : Orbit X T N hN)
    (U : Orbit X T P hP) (V : Orbit X T Q hQ)
    (hCD : ∀ i j, C.point i≠D.point j) (hUV : ∀ i j, U.point i≠V.point j)
    (hCU : ∀ i j, C.point i≠U.point j) (hCV : ∀ i j, C.point i≠V.point j)
    (hDU : ∀ i j, D.point i≠U.point j) (hDV : ∀ i j, D.point i≠V.point j) :
    let T' := splice (splice T (C.point (lastIndex hM)) (D.point (lastIndex hN)))
      (U.point (lastIndex hP)) (V.point (lastIndex hQ))
    Orbit X T' (M+N) (by omega) × Orbit X T' (P+Q) (by omega) := by
  let a := C.point (lastIndex hM)
  let b := D.point (lastIndex hN)
  let c := U.point (lastIndex hP)
  let d := V.point (lastIndex hQ)
  let J := joinedOrbit C D hCD
  let J' := J.outside_splice c d
    (joined_avoids C D c (fun i => hCU i (lastIndex hP)) (fun i => hDU i (lastIndex hP)))
    (joined_avoids C D d (fun i => hCV i (lastIndex hQ)) (fun i => hDV i (lastIndex hQ)))
  let U' := U.outside_splice a b (fun i => Ne.symm (hCU (lastIndex hM) i))
    (fun i => Ne.symm (hDU (lastIndex hN) i))
  let V' := V.outside_splice a b (fun i => Ne.symm (hCV (lastIndex hM) i))
    (fun i => Ne.symm (hDV (lastIndex hN) i))
  exact ⟨J',joinedOrbit U' V' hUV⟩

/-- Both outputs retain exactly their explicitly concatenated original clocks. -/
theorem doubleSplice_points {X : Type} [DecidableEq X] {T : X → X} {M N P Q : Nat}
    {hM : 0<M} {hN : 0<N} {hP : 0<P} {hQ : 0<Q}
    (C : Orbit X T M hM) (D : Orbit X T N hN)
    (U : Orbit X T P hP) (V : Orbit X T Q hQ)
    (hCD : ∀ i j, C.point i≠D.point j) (hUV : ∀ i j, U.point i≠V.point j)
    (hCU : ∀ i j, C.point i≠U.point j) (hCV : ∀ i j, C.point i≠V.point j)
    (hDU : ∀ i j, D.point i≠U.point j) (hDV : ∀ i j, D.point i≠V.point j)
    (i : Fin (M+N)) (j : Fin (P+Q)) :
    (doubleSplice C D U V hCD hUV hCU hCV hDU hDV).1.point i=joined C D i ∧
    (doubleSplice C D U V hCD hUV hCU hCV hDU hDV).2.point j=joined U V j := by
  exact ⟨rfl,rfl⟩

theorem doubleSplice_disjoint {X : Type} [DecidableEq X] {T : X → X} {M N P Q : Nat}
    {hM : 0<M} {hN : 0<N} {hP : 0<P} {hQ : 0<Q}
    (C : Orbit X T M hM) (D : Orbit X T N hN)
    (U : Orbit X T P hP) (V : Orbit X T Q hQ)
    (hCD : ∀ i j, C.point i≠D.point j) (hUV : ∀ i j, U.point i≠V.point j)
    (hCU : ∀ i j, C.point i≠U.point j) (hCV : ∀ i j, C.point i≠V.point j)
    (hDU : ∀ i j, D.point i≠U.point j) (hDV : ∀ i j, D.point i≠V.point j)
    (i : Fin (M+N)) (j : Fin (P+Q)) :
    (doubleSplice C D U V hCD hUV hCU hCV hDU hDV).1.point i≠
      (doubleSplice C D U V hCD hUV hCU hCV hDU hDV).2.point j := by
  intro he
  change joined C D i=joined U V j at he
  rcases (joined_image C D (joined U V j)).mp ⟨i,he⟩ with ⟨c,hc⟩ | ⟨d,hd⟩
  · rcases (joined_image U V (joined U V j)).mp ⟨j,rfl⟩ with ⟨u,hu⟩ | ⟨v,hv⟩
    · exact hCU c u (hc.trans hu.symm)
    · exact hCV c v (hc.trans hv.symm)
  · rcases (joined_image U V (joined U V j)).mp ⟨j,rfl⟩ with ⟨u,hu⟩ | ⟨v,hv⟩
    · exact hDU d u (hd.trans hu.symm)
    · exact hDV d v (hd.trans hv.symm)

#print axioms doubleSplice_disjoint
#print axioms doubleSplice
#print axioms closeAt
#print axioms closeAt_last
#print axioms Orbit.outside_splice
#print axioms joinedOrbit
#print axioms joined_image
#print axioms flip_transition

end ErdePaths.AACMerge
