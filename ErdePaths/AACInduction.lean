import ErdePaths.AACChain

namespace ErdePaths.AACInduction
open SquareLift AACTransition AACMerge AACChain

abbrev InOrbit {X : Type} {T : X→X} {N : Nat} {hN : 0<N}
    (C : Orbit X T N hN) (s : X) : Prop := ∃i, C.point i=s

private theorem recut_disjoint {X : Type} {T : X→X} {M N : Nat} {hM : 0<M} {hN : 0<N}
    (C : Orbit X T M hM) (D : Orbit X T N hN) (c : Fin M) (d : Fin N)
    (hd : ∀i j, C.point i≠D.point j) :
    ∀i j, (closeAt C c).point i≠(closeAt D d).point j := fun _ _ => hd _ _

/-- Literal row merger with cuts obtained from actual port occurrences.
Both new clocks and their INDIVIDUAL image sets are constructed. -/
theorem port_growth {K B M N P Q : Nat} (hK : 0<K) (hB : 0<B)
    (hM : 0<M) (hN : 0<N) (hP : 0<P) (hQ : 0<Q) (turns : Grid K B→Bool) (g : Grid K B)
    (C : Orbit (State K B) (transition hK hB turns) M hM)
    (D : Orbit (State K B) (transition hK hB turns) N hN)
    (U : Orbit (State K B) (transition hK hB turns) P hP)
    (V : Orbit (State K B) (transition hK hB turns) Q hQ)
    (hc : InOrbit C (g.1,g.2,.up)) (hd : InOrbit D (g.1,g.2,.down))
    (hu : InOrbit U (g.1,g.2,.left)) (hv : InOrbit V (g.1,g.2,.right))
    (hCD : ∀i j, C.point i≠D.point j) (hUV : ∀i j, U.point i≠V.point j)
    (hCU : ∀i j, C.point i≠U.point j) (hCV : ∀i j, C.point i≠V.point j)
    (hDU : ∀i j, D.point i≠U.point j) (hDV : ∀i j, D.point i≠V.point j) :
    ∃J : Orbit (State K B) (transition hK hB (flippedTurns turns g)) (M+N) (by omega),
    ∃J' : Orbit (State K B) (transition hK hB (flippedTurns turns g)) (P+Q) (by omega),
      (∀i j, J.point i≠J'.point j) ∧
      (∀s, InOrbit J s ↔ InOrbit C s ∨ InOrbit D s) ∧
      (∀s, InOrbit J' s ↔ InOrbit U s ∨ InOrbit V s) := by
  obtain ⟨c,hc⟩ := hc
  obtain ⟨d,hd⟩ := hd
  obtain ⟨u,hu⟩ := hu
  obtain ⟨v,hv⟩ := hv
  let C' := closeAt C c
  let D' := closeAt D d
  let U' := closeAt U u
  let V' := closeAt V v
  have cd := recut_disjoint C D c d hCD
  have uv := recut_disjoint U V u v hUV
  have cu := recut_disjoint C U c u hCU
  have cv := recut_disjoint C V c v hCV
  have du := recut_disjoint D U d u hDU
  have dv := recut_disjoint D V d v hDV
  let pair := doubleSplice C' D' U' V' cd uv cu cv du dv
  have eqT : splice (splice (transition hK hB turns)
      (C'.point (lastIndex hM)) (D'.point (lastIndex hN)))
      (U'.point (lastIndex hP)) (V'.point (lastIndex hQ)) =
      transition hK hB (flippedTurns turns g) := by
    change splice (splice (transition hK hB turns)
      ((closeAt C c).point (lastIndex hM)) ((closeAt D d).point (lastIndex hN)))
      ((closeAt U u).point (lastIndex hP)) ((closeAt V v).point (lastIndex hQ)) = _
    rw [closeAt_last,closeAt_last,closeAt_last,closeAt_last,hc,hd,hu,hv]
    funext s
    exact (flip_transition hK hB turns g s).symm
  have pdis : ∀i j, pair.1.point i≠pair.2.point j :=
    doubleSplice_disjoint C' D' U' V' cd uv cu cv du dv
  have pi (s : State K B) : InOrbit pair.1 s ↔ InOrbit C s ∨ InOrbit D s := by
    change (∃i, joined C' D' i=s) ↔ _
    rw [joined_image]
    exact or_congr (closeAt_image C c s) (closeAt_image D d s)
  have pj (s : State K B) : InOrbit pair.2 s ↔ InOrbit U s ∨ InOrbit V s := by
    change (∃i, joined U' V' i=s) ↔ _
    rw [joined_image]
    exact or_congr (closeAt_image U u s) (closeAt_image V v s)
  have out := (⟨pair.1,pair.2,pdis,pi,pj⟩ : ∃J : Orbit (State K B)
    (splice (splice (transition hK hB turns) (C'.point (lastIndex hM)) (D'.point (lastIndex hN)))
      (U'.point (lastIndex hP)) (V'.point (lastIndex hQ))) (M+N) (by omega),
    ∃J' : Orbit (State K B)
    (splice (splice (transition hK hB turns) (C'.point (lastIndex hM)) (D'.point (lastIndex hN)))
      (U'.point (lastIndex hP)) (V'.point (lastIndex hQ))) (P+Q) (by omega),
      (∀i j, J.point i≠J'.point j) ∧
      (∀s, InOrbit J s ↔ InOrbit C s ∨ InOrbit D s) ∧
      (∀s, InOrbit J' s ↔ InOrbit U s ∨ InOrbit V s))
  rw [eqT] at out
  exact out


def baselineClock {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K→Bool)
    (hb : BalancedTurns t) (rev : Bool) (label : Fin B) :
    Orbit (State K B) (transition hK hB (fun w => t w.1)) (2*K) (by omega) :=
  if rev then reverseBaseline hK hB t hb label else baselineOrbit hK hB t hb label

theorem clock_disjoint {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K→Bool)
    (hb : BalancedTurns t) {a b : Fin B} {r s : Bool}
    (hd : a≠b ∨ r≠s) (i j : Fin (2*K)) :
    (baselineClock hK hB t hb r a).point i ≠ (baselineClock hK hB t hb s b).point j := by
  cases r <;> cases s
  · apply baseline_disjoint hK hB t hb
    rcases hd with h | h
    · exact h
    · exact False.elim (h rfl)
  · exact positive_reverse_disjoint hK hB t hb _ _ _ _
  · exact Ne.symm (positive_reverse_disjoint hK hB t hb _ _ _ _)
  · apply reverse_disjoint hK hB t hb
    rcases hd with h | h
    · exact h
    · exact False.elim (h rfl)

def orientation (side : Bool) (label : Nat) : Bool := if label%2=0 then side else !side

def Prefix {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K→Bool)
    (hb : BalancedTurns t) (side : Bool) (k : Nat) (s : State K B) : Prop :=
  ∃a : Fin B, a.val≤k ∧ InOrbit (baselineClock hK hB t hb (orientation side a.val) a) s

theorem prefix_disjoint {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K→Bool)
    (hb : BalancedTurns t) (k : Nat) (s : State K B) :
    Prefix hK hB t hb false k s → ¬Prefix hK hB t hb true k s := by
  rintro ⟨a,ha,i,hi⟩ ⟨b,hb',j,hj⟩
  have hd : a≠b ∨ orientation false a.val≠orientation true b.val := by
    by_cases hab : a=b
    · subst b
      right
      by_cases he : a.val%2=0 <;> simp [orientation,he]
    · exact Or.inl hab
  exact clock_disjoint hK hB t hb hd i j (hi.trans hj.symm)

theorem prefix_fresh_disjoint {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K→Bool)
    (hb : BalancedTurns t) (side rev : Bool) (k : Nat) (a : Fin B) (ha : k<a.val)
    (s : State K B) : Prefix hK hB t hb side k s →
      ¬InOrbit (baselineClock hK hB t hb rev a) s := by
  rintro ⟨b,hb',i,hi⟩ ⟨j,hj⟩
  have hba : b≠a := by intro he; subst b; omega
  exact clock_disjoint hK hB t hb (Or.inl hba) i j (hi.trans hj.symm)

/-- Adding the next label has an exact individual orientation decomposition. -/
theorem prefix_succ {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K→Bool)
    (hb : BalancedTurns t) (side : Bool) (k : Nat) (hk : k+1<B) (s : State K B) :
    Prefix hK hB t hb side (k+1) s ↔ Prefix hK hB t hb side k s ∨
      InOrbit (baselineClock hK hB t hb (orientation side (k+1)) ⟨k+1,hk⟩) s := by
  constructor
  · rintro ⟨a,ha,hi⟩
    by_cases hak : a.val≤k
    · exact Or.inl ⟨a,hak,hi⟩
    · have hv : a.val=k+1 := by omega
      have he : a=⟨k+1,hk⟩ := Fin.ext hv
      subst a
      exact Or.inr hi
  · rintro (⟨a,ha,hi⟩ | hi)
    · exact ⟨a,by omega,hi⟩
    · exact ⟨⟨k+1,hk⟩,Nat.le_refl _,hi⟩

def downSide (k : Nat) : Bool := decide (k%2=1)

private theorem orientation_frontier (k : Nat) :
    orientation (downSide k) k=false ∧ orientation (!(downSide k)) k=true ∧
    orientation (downSide k) (k+1)=true ∧ orientation (!(downSide k)) (k+1)=false := by
  have hm := Nat.mod_lt k (by omega : 0<2)
  by_cases he : k%2=0
  · have ho : (k+1)%2=1 := by omega
    simp [orientation,downSide,he,ho]
  · have ho : k%2=1 := by omega
    have hn : (k+1)%2=0 := by omega
    simp [orientation,downSide,ho,hn]

/-- Concrete neighboring growth for either frontier parity. Exact prefix images
supply the cuts, and all six disjointness facts are derived from baseline labels.
Fresh clocks are the untouched next label under the current transition. -/
theorem growth_step {K B N : Nat} (hK : 0<K) (hB : 0<B) (hN : 0<N)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false)
    (k : Nat) (hk : k+1<B) (turns : Grid K B→Bool)
    (G : Bool→Orbit (State K B) (transition hK hB turns) N hN)
    (gi : ∀side s, InOrbit (G side) s ↔ Prefix hK hB t hb side k s)
    (F : Bool→Orbit (State K B) (transition hK hB turns) (2*K) (by omega))
    (fi : ∀rev i, (F rev).point i=(baselineClock hK hB t hb rev ⟨k+1,hk⟩).point i) :
    ∃J : Orbit (State K B)
        (transition hK hB (flippedTurns turns (⟨0,hK⟩,⟨k,by omega⟩))) (2*K+N) (by omega),
    ∃J' : Orbit (State K B)
        (transition hK hB (flippedTurns turns (⟨0,hK⟩,⟨k,by omega⟩))) (N+2*K) (by omega),
      (∀i j, J.point i≠J'.point j) ∧
      (∀s, InOrbit J s ↔ Prefix hK hB t hb (downSide k) (k+1) s) ∧
      (∀s, InOrbit J' s ↔ Prefix hK hB t hb (!(downSide k)) (k+1) s) := by
  let j : Fin B := ⟨k,by omega⟩
  let a : Fin B := ⟨k+1,hk⟩
  have hs : successor hB j=a := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hk
  have hp := zero_ports hK hB t hb ht j
  rw [hs] at hp
  have ho := orientation_frontier k
  have hf (r : Bool) (s : State K B) : InOrbit (F r) s ↔
      InOrbit (baselineClock hK hB t hb r a) s := by
    constructor
    · rintro ⟨i,hi⟩; exact ⟨i,(fi r i).symm.trans hi⟩
    · rintro ⟨i,hi⟩; exact ⟨i,(fi r i).trans hi⟩
  have down : InOrbit (G (downSide k)) (⟨0,hK⟩,j,.down) := by
    apply (gi _ _).mpr
    refine ⟨j,Nat.le_refl _,?_⟩
    change InOrbit (baselineClock hK hB t hb (orientation (downSide k) k) j) _
    rw [ho.1]
    exact ⟨CubeCycle.index hK (⟨0,hK⟩,false),hp.1⟩
  have left : InOrbit (G (!(downSide k))) (⟨0,hK⟩,j,.left) := by
    apply (gi _ _).mpr
    refine ⟨j,Nat.le_refl _,?_⟩
    change InOrbit (baselineClock hK hB t hb (orientation (!(downSide k)) k) j) _
    rw [ho.2.1]
    exact ⟨(CubeCycle.index hK (⟨0,hK⟩,false)).rev,hp.2.2.1⟩
  have up : InOrbit (F true) (⟨0,hK⟩,j,.up) :=
    (hf _ _).mpr ⟨(CubeCycle.index hK (⟨0,hK⟩,true)).rev,hp.2.2.2⟩
  have right : InOrbit (F false) (⟨0,hK⟩,j,.right) :=
    (hf _ _).mpr ⟨CubeCycle.index hK (⟨0,hK⟩,true),hp.2.1⟩
  have gf (side r : Bool) (i : Fin N) (n : Fin (2*K)) :
      (G side).point i≠(F r).point n := by
    intro he
    have gp := (gi side ((G side).point i)).mp ⟨i,rfl⟩
    have fp := (hf r ((G side).point i)).mp ⟨n,he.symm⟩
    exact prefix_fresh_disjoint hK hB t hb side r k a (by change k<k+1; omega) _ gp fp
  have gg (i l : Fin N) : (G (downSide k)).point i≠(G (!(downSide k))).point l := by
    intro he
    have p := (gi (downSide k) ((G (downSide k)).point i)).mp ⟨i,rfl⟩
    have q := (gi (!(downSide k)) ((G (downSide k)).point i)).mp ⟨l,he.symm⟩
    cases hc : downSide k
    · simp only [hc,Bool.not_false] at p q
      exact prefix_disjoint hK hB t hb k _ p q
    · simp only [hc,Bool.not_true] at p q
      exact prefix_disjoint hK hB t hb k _ q p
  have ff (i l : Fin (2*K)) : (F true).point i≠(F false).point l := by
    rw [fi,fi]
    exact clock_disjoint hK hB t hb (Or.inr (by decide)) _ _
  obtain ⟨J,J',jd,ji,jj⟩ := port_growth hK hB (by omega) hN hN (by omega) turns
    (⟨0,hK⟩,j) (F true) (G (downSide k)) (G (!(downSide k))) (F false)
    up down left right (fun i l => Ne.symm (gf _ _ l i)) (gf _ _)
    (fun i l => Ne.symm (gf _ _ l i)) ff gg (gf _ _)
  refine ⟨J,J',jd,?_,?_⟩
  · intro s
    rw [ji,gi,hf, prefix_succ hK hB t hb (downSide k) k hk s]
    change InOrbit (baselineClock hK hB t hb true a) s ∨ Prefix hK hB t hb (downSide k) k s ↔
      Prefix hK hB t hb (downSide k) k s ∨ InOrbit (baselineClock hK hB t hb (orientation (downSide k) (k+1)) a) s
    rw [ho.2.2.1]
    exact or_comm
  · intro s
    rw [jj,gi,hf,prefix_succ hK hB t hb (!(downSide k)) k hk s]
    change Prefix hK hB t hb (!(downSide k)) k s ∨ InOrbit (baselineClock hK hB t hb false a) s ↔
      Prefix hK hB t hb (!(downSide k)) k s ∨ InOrbit (baselineClock hK hB t hb (orientation (!(downSide k)) (k+1)) a) s
    rw [ho.2.2.2]


/-- The literal prescribed turns after flipping exactly rows below n. -/
def turnsAfter {K B : Nat} (hK : 0<K) (t : Fin K→Bool) (n : Nat) (g : Grid K B) : Bool :=
  if g.1=⟨0,hK⟩ ∧ g.2.val<n then !(t g.1) else t g.1

theorem turnsAfter_zero {K B : Nat} (hK : 0<K) (t : Fin K→Bool) :
    turnsAfter (B := B) hK t 0=(fun g => t g.1) := by
  funext g
  simp [turnsAfter]

theorem turnsAfter_step {K B : Nat} (hK : 0<K) (t : Fin K→Bool)
    (n : Nat) (hn : n<B) :
    flippedTurns (turnsAfter hK t n) (⟨0,hK⟩,⟨n,hn⟩)=turnsAfter hK t (n+1) := by
  funext g
  by_cases hi : g.1=⟨0,hK⟩
  · by_cases hj : g.2.val=n
    · have hg : g=(⟨0,hK⟩,⟨n,hn⟩) := Prod.ext hi (Fin.ext hj)
      subst g
      simp [flippedTurns,turnsAfter]
    · have hg : g≠(⟨0,hK⟩,⟨n,hn⟩) := by
        intro he
        exact hj (congrArg (fun g : Grid K B => g.2.val) he)
      have hlt : (g.2.val<n)=(g.2.val<n+1) := propext (by omega)
      simp only [flippedTurns,ite_eq_right hg,turnsAfter,hi,true_and,hlt]
  · have hg : g≠(⟨0,hK⟩,⟨n,hn⟩) := fun he => hi (congrArg Prod.fst he)
    simp [flippedTurns,turnsAfter,hi,hg]

/-- Preservation at an additional row flip, derived for a literal untouched
baseline point map rather than assumed for later clocks. -/
theorem preserve_fresh {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false)
    (turns : Grid K B→Bool) (j a : Fin B) (rev : Bool)
    (C : Orbit (State K B) (transition hK hB turns) (2*K) (by omega))
    (ci : ∀i, C.point i=(baselineClock hK hB t hb rev a).point i)
    (haj : a≠j) (has : a≠successor hB j) :
    ∃D : Orbit (State K B)
      (transition hK hB (flippedTurns turns (⟨0,hK⟩,j))) (2*K) (by omega),
      ∀i, D.point i=(baselineClock hK hB t hb rev a).point i := by
  have hp := zero_ports hK hB t hb ht j
  have avoid (b : Fin B) (r : Bool) (hab : a≠b) (i l : Fin (2*K)) :
      C.point i≠(baselineClock hK hB t hb r b).point l := by
    rw [ci]
    exact clock_disjoint hK hB t hb (Or.inl hab) _ _
  have ha : ∀i, C.point i≠(⟨0,hK⟩,j,Port.up) := by
    intro i
    rw [←hp.2.2.2]
    exact avoid _ true has _ _
  have hd : ∀i, C.point i≠(⟨0,hK⟩,j,Port.down) := by
    intro i; rw [←hp.1]; exact avoid _ false haj _ _
  have hl : ∀i, C.point i≠(⟨0,hK⟩,j,Port.left) := by
    intro i; rw [←hp.2.2.1]; exact avoid _ true haj _ _
  have hr : ∀i, C.point i≠(⟨0,hK⟩,j,Port.right) := by
    intro i; rw [←hp.2.1]; exact avoid _ false has _ _
  obtain ⟨D,di⟩ := away_flip hK hB (by omega) turns (⟨0,hK⟩,j) C ha hd hl hr
  exact ⟨D,fun i => (di i).trans (ci i)⟩

/-- Inductive data consists of constructed clocks, exact individual image
invariants and the actually preserved unprocessed baseline clocks. -/
def Stage {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K→Bool)
    (hb : BalancedTurns t) (n : Nat) : Prop :=
  ∃G : Bool→Orbit (State K B) (transition hK hB (turnsAfter hK t n))
      ((n+1)*(2*K)) (Nat.mul_pos (by omega) (by omega)),
    (∀side s, InOrbit (G side) s ↔ Prefix hK hB t hb side n s) ∧
    (∀a : Fin B, n<a.val → ∀rev,
      ∃F : Orbit (State K B) (transition hK hB (turnsAfter hK t n)) (2*K) (by omega),
        ∀i, F.point i=(baselineClock hK hB t hb rev a).point i)


private def resizeOrbit {X : Type} {T : X→X} {N M : Nat} {hN : 0<N} {hM : 0<M}
    (C : Orbit X T N hN) (e : N=M) : Orbit X T M hM := by
  subst M
  exact C

private theorem resize_image {X : Type} {T : X→X} {N M : Nat} {hN : 0<N} {hM : 0<M}
    (C : Orbit X T N hN) (e : N=M) (s : X) :
    InOrbit (resizeOrbit (hM := hM) C e) s ↔ InOrbit C s := by
  subst M
  rfl

/-- Actual finite construction of every stage of the prescribed nonwrapping
chain. There is no merged-orbit or existence assumption. -/
theorem stages {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) :
    ∀n, n<B → Stage hK hB t hb n := by
  intro n
  induction n with
  | zero =>
    intro hn
    unfold Stage
    rw [turnsAfter_zero]
    let G (side : Bool) := resizeOrbit (hM := Nat.mul_pos (by omega) (by omega))
      (baselineClock hK hB t hb side ⟨0,hB⟩) (show 2*K=(0+1)*(2*K) by simp)
    refine ⟨G,?_,?_⟩
    · intro side s
      change InOrbit (resizeOrbit _ _) s ↔ _
      rw [resize_image]
      constructor
      · intro hi
        refine ⟨⟨0,hB⟩,Nat.le_refl _,?_⟩
        simpa only [orientation,Nat.zero_mod,↓reduceIte] using hi
      · rintro ⟨a,ha,hi⟩
        change a.val≤0 at ha
        have he : a=⟨0,hB⟩ := Fin.ext (by change a.val=0; omega)
        subst a
        simpa only [orientation,Nat.zero_mod,↓reduceIte] using hi
    · intro a ha rev
      exact ⟨baselineClock hK hB t hb rev a,fun _ => rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨G,gi,fresh⟩ := ih (by omega)
    let a : Fin B := ⟨n+1,hn⟩
    have ha : n<a.val := by change n<n+1; omega
    let F (r : Bool) := Classical.choose (fresh a ha r)
    have fi (r : Bool) (i : Fin (2*K)) : (F r).point i=
        (baselineClock hK hB t hb r a).point i := Classical.choose_spec (fresh a ha r) i
    obtain ⟨J,J',jd,ji,jj⟩ := growth_step hK hB (Nat.mul_pos (by omega) (by omega))
      t hb ht n hn (turnsAfter hK t n) G gi F fi
    have e : 2*K+(n+1)*(2*K)=(n+1+1)*(2*K) := by
      calc
        _ = (n+1)*(2*K)+1*(2*K) := by simp only [Nat.one_mul]; exact Nat.add_comm _ _
        _ = (n+1+1)*(2*K) := (Nat.add_mul _ _ _).symm
    have e' : (n+1)*(2*K)+2*K=(n+1+1)*(2*K) := by
      simpa only [Nat.one_mul] using (Nat.add_mul (n+1) 1 (2*K)).symm
    unfold Stage
    rw [←turnsAfter_step hK t n (by omega)]
    let G' (side : Bool) := if side=downSide n then
      resizeOrbit (hM := Nat.mul_pos (by omega) (by omega)) J e else
      resizeOrbit (hM := Nat.mul_pos (by omega) (by omega)) J' e'
    refine ⟨G',?_,?_⟩
    · intro side s
      by_cases he : side=downSide n
      · subst side
        change InOrbit (if downSide n=downSide n then _ else _) s ↔ _
        rw [ite_eq_left rfl,resize_image,ji]
      · have hs : side=!(downSide n) := by cases side <;> cases h : downSide n <;> simp_all
        change InOrbit (if side=downSide n then _ else _) s ↔ _
        rw [ite_eq_right he,resize_image,jj,hs]
    · intro b hb' r
      obtain ⟨C,ci⟩ := fresh b (by omega) r
      have hbj : b≠(⟨n,by omega⟩ : Fin B) := by
        intro he
        have hv := congrArg Fin.val he
        change b.val=n at hv
        omega
      have hbs : b≠successor hB (⟨n,by omega⟩ : Fin B) := by
        intro he
        have hv := congrArg Fin.val he
        change b.val=(n+1)%B at hv
        rw [Nat.mod_eq_of_lt hn] at hv
        omega
      exact preserve_fresh hK hB t hb ht (turnsAfter hK t n) ⟨n,by omega⟩ b r C ci hbj hbs


theorem prefix_full {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (s : State K B) :
    Prefix hK hB t hb false (B-1) s ∨ Prefix hK hB t hb true (B-1) s := by
  obtain ⟨a,ha | ha⟩ := baseline_covers hK hB t hb s
  · by_cases he : a.val%2=0
    · left
      refine ⟨a,by have := a.isLt; omega,?_⟩
      simpa only [orientation,he,↓reduceIte,baselineClock,Bool.false_eq_true] using ha
    · right
      refine ⟨a,by have := a.isLt; omega,?_⟩
      simpa only [orientation,he,↓reduceIte,Bool.not_true,baselineClock,Bool.false_eq_true] using ha
  · by_cases he : a.val%2=0
    · right
      refine ⟨a,by have := a.isLt; omega,?_⟩
      simpa only [orientation,he,↓reduceIte,baselineClock] using ha
    · left
      refine ⟨a,by have := a.isLt; omega,?_⟩
      simpa only [orientation,he,↓reduceIte,Bool.not_false,baselineClock] using ha

/-- All B−1 actual row switches are constructed. The two injective directed
clocks have length 2KB and partition the complete physical port-state set.
This does not by itself assert vertex simplicity of the Euler word. -/
theorem full_chain {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) :
    ∃G : Bool→Orbit (State K B) (transition hK hB (turnsAfter hK t (B-1)))
        (B*(2*K)) (Nat.mul_pos hB (by omega)),
      (∀side s, InOrbit (G side) s ↔ Prefix hK hB t hb side (B-1) s) ∧
      (∀i j, (G false).point i≠(G true).point j) ∧
      (∀s, InOrbit (G false) s ∨ InOrbit (G true) s) := by
  obtain ⟨G,gi,tail⟩ := stages hK hB t hb ht (B-1) (by omega)
  have gd (i j) : (G false).point i≠(G true).point j := by
    intro he
    have p := (gi false ((G false).point i)).mp ⟨i,rfl⟩
    have q := (gi true ((G false).point i)).mp ⟨j,he.symm⟩
    exact prefix_disjoint hK hB t hb (B-1) _ p q
  have gc (s : State K B) : InOrbit (G false) s ∨ InOrbit (G true) s := by
    rcases prefix_full hK hB t hb s with hp | hp
    · exact Or.inl ((gi _ _).mpr hp)
    · exact Or.inr ((gi _ _).mpr hp)
  have he : (B-1+1)*(2*K)=B*(2*K) := congrArg (fun n => n*(2*K)) (show B-1+1=B by omega)
  let G' (side : Bool) := resizeOrbit (hM := Nat.mul_pos hB (by omega)) (G side) he
  have g'i (side : Bool) (s : State K B) : InOrbit (G' side) s ↔ Prefix hK hB t hb side (B-1) s := by
    change InOrbit (resizeOrbit _ he) s ↔ _
    rw [resize_image,gi]
  refine ⟨G',g'i,?_,?_⟩
  · intro i j h
    exact prefix_disjoint hK hB t hb (B-1) _
      ((g'i false ((G' false).point i)).mp ⟨i,rfl⟩) ((g'i true ((G' false).point i)).mp ⟨j,h.symm⟩)
  · intro s
    rcases prefix_full hK hB t hb s with hp | hp
    · exact Or.inl ((g'i _ _).mpr hp)
    · exact Or.inr ((g'i _ _).mpr hp)

#print axioms port_growth
#print axioms growth_step
#print axioms stages
#print axioms full_chain

end ErdePaths.AACInduction
