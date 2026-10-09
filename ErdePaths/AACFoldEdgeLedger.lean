import ErdePaths.AACFoldClock

namespace ErdePaths.AACFoldEdgeLedger
open SubdividedWiggle SquareLift PairedLayers LayerOwnership LayerPartition AACIntervalSplit AACFoldOrder AACFoldGeometry
variable {E r : Nat} {X Y : Type} {R : X→X→Prop} {χ : X→Bool} {hr : 0<r}

/-- Canonical input edge identities retain every chronological base edge,
including repeated physical base vertices. -/
abbrev InputLabel (S : Fin E→Bool) (r : Nat) (X : Type) :=
  (Fin (Profile.cardinality S) × Bool × Fin r) ⊕ (Fin E × X)

noncomputable def gapInverse (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (n : Fin E) : GapPosition S := Classical.choose (gapIndex_surjective hE S hzero n)

theorem gapInverse_index (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (n : Fin E) : gapIndex S (gapInverse hE S hzero n)=n :=
  Classical.choose_spec (gapIndex_surjective hE S hzero n)

theorem gapInverse_gap (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (p : GapPosition S) : gapInverse hE S hzero (gapIndex S p)=p :=
  gapIndex_injective S (gapInverse_index hE S hzero _)

/-- Actual canonical physical host edges, before output tours are used. -/
noncomputable def decode (hE : 0<E) (S : Fin E→Bool) (base : Fin E→Y)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr) :
    InputLabel S r X → (Y×X)×(Y×X)
  | .inl (j,a,t) => ((base (markIndex S j),(layers j).vertex (t,false)),
      (base (markIndex S j),choose (layers j) a ((layers j).vertex (t,false))))
  | .inr (n,x) => ((base n,x),(base (successor hE n),x))

/-- Local outgoing edge in actual expanded physical coordinates. -/
noncomputable def outgoing (S : Fin E→Bool) (base : Fin E→Y)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (e : Bool × FoldPosition (r:=r) S) : (Y×X)×(Y×X) :=
  (foldVertex S base C layers selectors e.1 e.2,
   foldVertex S base C layers selectors e.1 (foldNext hr S hq e.2))

noncomputable def encode (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool)
    (e : Bool × FoldPosition (r:=r) S) : InputLabel S r X :=
  if e.2.1.2.2.val=0 then
    let j := e.2.1.2.1
    let a := selectors j ^^ e.1
    let y := arrival C layers selectors e.1 j e.2.1.1
    .inl (j,a,((layers j).coordinate (canonical (layers j) a y)).1)
  else .inr (foldBase S e.2,foldJ S C layers selectors e.1 e.2)

theorem outgoing_arrival (S : Fin E→Bool) (base : Fin E→Y)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (e : Bool × FoldPosition (r:=r) S) (hb : e.2.1.2.2.val=0) :
    outgoing S base C layers selectors hq e =
      ((base (markIndex S e.2.1.2.1),arrival C layers selectors e.1 e.2.1.2.1 e.2.1.1),
       (base (markIndex S e.2.1.2.1),departure C layers selectors e.1 e.2.1.2.1 e.2.1.1)) := by
  rcases e with ⟨color,⟨⟨t,j,b⟩,k⟩⟩
  have he : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb
  subst b
  have hk : k.val=0 := by have := k.isLt; simp [foldWeight] at this; omega
  have hn : ¬k.val+1<foldWeight S (t,j,(⟨0,by decide⟩ : Fin 2)) := by simp [foldWeight,hk]
  unfold outgoing foldVertex
  rw [foldNext,dite_eq_right hn]
  simp [foldBase,foldJ,Wiggle.coordinateNext,
    LayerTour.flagCoordinates,LayerTour.flagBool,commonTour,gapIndex]

theorem outgoing_departure (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (base : Fin E→Y) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (hreturn : ∀color t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color))
    (e : Bool × FoldPosition (r:=r) S) (hb : e.2.1.2.2.val≠0) :
    outgoing S base C layers selectors hq e =
      ((base (foldBase S e.2),foldJ S C layers selectors e.1 e.2),
       (base (successor hE (foldBase S e.2)),foldJ S C layers selectors e.1 e.2)) := by
  unfold outgoing foldVertex
  by_cases hn : e.2.2.val+1<foldWeight S e.2.1
  · rw [foldBase_internal hE hr S hq e.2 hb hn,
      foldJ_internal S C layers selectors e.1 hq e.2 hn]
  · rw [foldBase_boundary hE hr S hzero hq e.2 hb hn,
      foldJ_boundary S C layers selectors e.1 hq (hreturn e.1) e.2 hb hn]

private theorem canonical_vertex (D : CycleData X R χ r hr) (a : Bool) (x : X) :
    D.vertex ((D.coordinate (canonical D a x)).1,false)=canonical D a x := by
  have hc := congrArg χ (D.vertex_coordinate (canonical D a x))
  rw [D.bipartition,canonical_side D a x] at hc
  rw [←hc]
  exact D.vertex_coordinate _

theorem encode_decodes (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (base : Fin E→Y) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (hreturn : ∀color t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color)) (e : Bool × FoldPosition (r:=r) S) :
    SameEdge (decode hE S base layers (encode S C layers selectors e))
      (outgoing S base C layers selectors hq e) := by
  by_cases hb : e.2.1.2.2.val=0
  · rw [outgoing_arrival S base C layers selectors hq e hb]
    simp only [encode,hb,↓reduceIte,decode]
    rw [canonical_vertex]
    exact map_sameEdge (fun x => (base (markIndex S e.2.1.2.1),x))
      (canonical_edge (layers e.2.1.2.1) (selectors e.2.1.2.1 ^^ e.1)
        (arrival C layers selectors e.1 e.2.1.2.1 e.2.1.1))
  · rw [outgoing_departure hE S hzero base C layers selectors hq hreturn e hb]
    simp only [encode,hb,↓reduceIte,decode]
    exact Or.inl rfl

private theorem flipN_self (n : Nat) (b : Bool) : flipN n (flipN n b)=b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change flipN n (!(flipN n (!b)))=b
    rw [←flipN_not,Bool.not_not,ih]

/-- Every physical X vertex occurs in exactly one complementary departure
side at each interval. -/
theorem departure_cover (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool)
    (j : Fin (Profile.cardinality S)) (x : X) :
    ∃color t, departure C layers selectors color j t=x := by
  let color := flipN j.val (!χ x)
  have hx : χ x= !flipN j.val color := by
    dsimp only [color]
    rw [flipN_self,Bool.not_not]
  obtain ⟨t,ht⟩ := departure_covers_side C layers selectors color j x hx
  exact ⟨color,t,ht⟩

/-- No canonical host edge label is omitted by the actual ragged tours. -/
theorem encode_surjective (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) :
    Function.Surjective (encode S C layers selectors) := by
  intro f
  cases f with
  | inl f =>
    obtain ⟨⟨color,t,j,b⟩,he⟩ := encodeLabel_surjective C layers selectors (.inl f)
    cases b with
    | true => cases he
    | false =>
      let p : FoldPosition (r:=r) S := ⟨(t,j,⟨0,by decide⟩),⟨0,by simp [foldWeight]⟩⟩
      refine ⟨(color,p),?_⟩
      simpa [encode,encodeLabel,p] using he
  | inr f =>
    rcases f with ⟨n,x⟩
    let g := gapInverse hE S hzero n
    obtain ⟨color,t,ht⟩ := departure_cover C layers selectors g.1 x
    let p : FoldPosition (r:=r) S :=
      ⟨(t,g.1,⟨1,by decide⟩),⟨g.2.val,by simp [foldWeight]⟩⟩
    refine ⟨(color,p),?_⟩
    change Sum.inr (gapIndex S g,departure C layers selectors color g.1 t)=Sum.inr (n,x)
    rw [gapInverse_index,ht]

/-- The actual local edge identities are bijective before any ambient host
edge uniqueness hypothesis is used. -/
theorem encode_injective (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) :
    Function.Injective (encode S C layers selectors) := by
  intro e f he
  rcases e with ⟨c,⟨⟨t,j,b⟩,k⟩⟩
  rcases f with ⟨d,⟨⟨u,l,a⟩,z⟩⟩
  by_cases hb : b.val=0
  · by_cases ha : a.val=0
    · have be : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb
      have ae : a=(⟨0,by decide⟩ : Fin 2) := Fin.ext ha
      subst b; subst a
      have hk : k.val=0 := by have := k.isLt; simp [foldWeight] at this; omega
      have hz : z.val=0 := by have := z.isLt; simp [foldWeight] at this; omega
      have hh : encodeLabel C layers selectors (c,t,j,false)=
          encodeLabel C layers selectors (d,u,l,false) := by
        simpa [encode,encodeLabel] using he
      have hpos := encodeLabel_injective C layers selectors hh
      have hc := congrArg Prod.fst hpos
      have ht := congrArg (fun p : OutputLabel (Profile.cardinality S) r => p.2.1) hpos
      have hj := congrArg (fun p : OutputLabel (Profile.cardinality S) r => p.2.2.1) hpos
      have hcd : c=d := hc
      subst d
      exact congrArg (fun p : FoldPosition (r:=r) S => (c,p))
        (foldPosition_ext S _ _ ht hj rfl (show k.val=z.val from hk.trans hz.symm))
    · simp only [encode,hb,ha,↓reduceIte] at he
      cases he
  · by_cases ha : a.val=0
    · simp only [encode,hb,ha,↓reduceIte] at he
      cases he
    · have bv : b.val=1 := by have := b.isLt; omega
      have av : a.val=1 := by have := a.isLt; omega
      have be : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext bv
      have ae : a=(⟨1,by decide⟩ : Fin 2) := Fin.ext av
      subst b; subst a
      simp only [encode,show ¬(1:Nat)=0 by decide,↓reduceIte,Sum.inr.injEq,Prod.mk.injEq] at he
      have hgap := gapIndex_injective S he.1
      have hj := congrArg Sigma.fst hgap
      have hk := congrArg (fun p : GapPosition S => p.2.val) hgap
      change j=l at hj
      subst l
      have hx : departure C layers selectors c j t=departure C layers selectors d j u := he.2
      have hs := congrArg χ hx
      rw [departure_side C layers selectors c j t,departure_side C layers selectors d j u] at hs
      have hc : c=d := flipN_injective j.val (Bool.not_inj hs)
      subst d
      have ht := departure_injective C layers selectors c j hx
      exact congrArg (fun p : FoldPosition (r:=r) S => (c,p))
        (foldPosition_ext S _ _ ht rfl rfl hk)

/-- Parallel occurrences are retained until actual base edge uniqueness is
supplied; marked-vertex uniqueness likewise is an input base geometric law. -/
theorem decode_unique (hE : 0<E) (h2 : 2≤r) (S : Fin E→Bool) (base : Fin E→Y)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (hmarks : Function.Injective (fun j => base (markIndex S j)))
    (hbase : ∀n m, SameEdge (base n,base (successor hE n))
      (base m,base (successor hE m)) → n=m)
    (e f : InputLabel S r X)
    (he : SameEdge (decode hE S base layers e) (decode hE S base layers f)) : e=f := by
  cases e with
  | inl e =>
    rcases e with ⟨j,a,t⟩
    cases f with
    | inl f =>
      rcases f with ⟨k,b,z⟩
      have hj : j=k := by
        apply hmarks
        rcases he with he | he <;> exact congrArg (fun e => e.1.1) he
      subst k
      have hm := map_sameEdge Prod.snd he
      change SameEdge (matchingPair (layers j) a t) (matchingPair (layers j) b z) at hm
      obtain ⟨hab,htz⟩ := matchingPair_unique h2 (layers j) a b t z hm
      subst b; subst z; rfl
    | inr f =>
      rcases f with ⟨n,x⟩
      have hm := map_sameEdge Prod.snd he
      change SameEdge ((layers j).vertex (t,false),choose (layers j) a ((layers j).vertex (t,false))) (x,x) at hm
      rcases hm with hm | hm
      all_goals
        have hfirst := congrArg (fun p : X×X => χ p.1) hm
        have hsecond := congrArg (fun p : X×X => χ p.2) hm
        simp only [(layers j).bipartition,choose_flips] at hfirst hsecond
        exact Bool.noConfusion (hfirst.trans hsecond.symm)
  | inr e =>
    rcases e with ⟨n,x⟩
    cases f with
    | inl f =>
      rcases f with ⟨j,a,t⟩
      have hm := map_sameEdge Prod.snd (sameEdge_symm he)
      change SameEdge ((layers j).vertex (t,false),choose (layers j) a ((layers j).vertex (t,false))) (x,x) at hm
      rcases hm with hm | hm
      all_goals
        have hfirst := congrArg (fun p : X×X => χ p.1) hm
        have hsecond := congrArg (fun p : X×X => χ p.2) hm
        simp only [(layers j).bipartition,choose_flips] at hfirst hsecond
        exact Bool.noConfusion (hfirst.trans hsecond.symm)
    | inr f =>
      rcases f with ⟨m,y⟩
      have hn := hbase n m (map_sameEdge Prod.fst he)
      have hx : x=y := by
        rcases he with he | he <;> exact congrArg (fun p => p.1.2) he
      subst m; subst y; rfl

/-- The exact input host is the union of all displayed base edges at every
X vertex, and all displayed assigned-cycle edges at their literal marks. -/
def HostAdjacent (hE : 0<E) (S : Fin E→Bool) (base : Fin E→Y)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (u v : Y×X) : Prop := ∃e : InputLabel S r X, SameEdge (decode hE S base layers e) (u,v)

/-- Genuine physical undirected edge partition by the actual two ragged
output orders. The return law concerns the input matching schedule only. -/
theorem local_partition (hE : 0<E) (h2 : 2≤r) (S : Fin E→Bool)
    (hzero : S ⟨0,hE⟩=true) (base : Fin E→Y)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (hreturn : ∀color t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color))
    (hmarks : Function.Injective (fun j => base (markIndex S j)))
    (hbase : ∀n m, SameEdge (base n,base (successor hE n))
      (base m,base (successor hE m)) → n=m) :
    (∀u v, HostAdjacent hE S base layers u v →
      ∃e : Bool × FoldPosition (r:=r) S, SameEdge (outgoing S base C layers selectors hq e) (u,v)) ∧
    (∀e f, SameEdge (outgoing S base C layers selectors hq e)
      (outgoing S base C layers selectors hq f) → e=f) := by
  constructor
  · intro u v hh
    obtain ⟨a,ha⟩ := hh
    obtain ⟨e,he⟩ := encode_surjective hE S hzero C layers selectors a
    refine ⟨e,?_⟩
    have hd := encode_decodes hE S hzero base C layers selectors hq hreturn e
    rw [he] at hd
    exact sameEdge_trans (sameEdge_symm hd) ha
  · intro e f he
    apply encode_injective S C layers selectors
    exact decode_unique hE h2 S base layers hmarks hbase _ _
      (sameEdge_trans (encode_decodes hE S hzero base C layers selectors hq hreturn e)
        (sameEdge_trans he (sameEdge_symm (encode_decodes hE S hzero base C layers selectors hq hreturn f))))

noncomputable def numericOutgoing (hr : 0<r) (S : Fin E→Bool) (base : Fin E→Y)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (e : Bool × Fin (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length) :
    (Y×X)×(Y×X) :=
  (foldVertex S base C layers selectors e.1 (AACFoldClock.numeric S hq e.2),
   foldVertex S base C layers selectors e.1 (AACFoldClock.numeric S hq
     (successor (AACFoldClock.length_pos hr S hq) e.2)))

theorem numericOutgoing_eq (hr : 0<r) (S : Fin E→Bool) (base : Fin E→Y)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (e : Bool × Fin (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length) :
    numericOutgoing hr S base C layers selectors hq e =
      outgoing S base C layers selectors hq (e.1,AACFoldClock.numeric S hq e.2) := by
  unfold numericOutgoing outgoing
  rw [AACFoldClock.numeric_next]

/-- Partition for literal successive NUMERIC physical vertices, including
both outputs' final cyclic seams. -/
theorem numeric_partition (hE : 0<E) (h2 : 2≤r) (S : Fin E→Bool)
    (hzero : S ⟨0,hE⟩=true) (base : Fin E→Y)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (hreturn : ∀color t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color))
    (hmarks : Function.Injective (fun j => base (markIndex S j)))
    (hbase : ∀n m, SameEdge (base n,base (successor hE n))
      (base m,base (successor hE m)) → n=m) :
    (∀u v, HostAdjacent hE S base layers u v →
      ∃e, SameEdge (numericOutgoing hr S base C layers selectors hq e) (u,v)) ∧
    (∀e f, SameEdge (numericOutgoing hr S base C layers selectors hq e)
      (numericOutgoing hr S base C layers selectors hq f) → e=f) ∧
    (∀e, HostAdjacent hE S base layers
      (numericOutgoing hr S base C layers selectors hq e).1
      (numericOutgoing hr S base C layers selectors hq e).2) := by
  have hp := local_partition hE h2 S hzero base C layers selectors hq hreturn hmarks hbase
  constructor
  · intro u v hv
    obtain ⟨⟨color,p⟩,he⟩ := hp.1 u v hv
    obtain ⟨n,hn⟩ := AACFoldClock.numeric_surjective S hq p
    refine ⟨(color,n),?_⟩
    rw [numericOutgoing_eq,hn]
    exact he
  · constructor
    · intro e f he
      rw [numericOutgoing_eq,numericOutgoing_eq] at he
      have hh := hp.2 _ _ he
      have hc : e.1=f.1 := congrArg (fun p : Bool × FoldPosition (r:=r) S => p.1) hh
      have hn : e.2=f.2 := AACFoldClock.numeric_injective S hq (congrArg (fun p : Bool × FoldPosition (r:=r) S => p.2) hh)
      exact Prod.ext hc hn
    · intro e
      rw [numericOutgoing_eq]
      exact ⟨encode S C layers selectors (e.1,AACFoldClock.numeric S hq e.2),
        encode_decodes hE S hzero base C layers selectors hq hreturn _⟩

/-- An assigned input cycle's actual undirected edges. -/
def CycleAdjacent (D : CycleData X R χ r hr) (u v : X) : Prop :=
  ∃a t, SameEdge (matchingPair D a t) (u,v)

/-- Physical host specified using an ambient base graph Q and the actual
assigned input cycles, independently of all output tours. -/
def InputHost (Q : Y→Y→Prop) (S : Fin E→Bool) (base : Fin E→Y)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr) (u v : Y×X) : Prop :=
  (u.2=v.2 ∧ Q u.1 v.1) ∨
    ∃j, u.1=base (markIndex S j) ∧ v.1=base (markIndex S j) ∧ CycleAdjacent (layers j) u.2 v.2

/-- Exact equivalence with the literal input graph, using only the base
Euler edge ledger. No output edge-cover premise is involved. -/
theorem host_iff (hE : 0<E) (S : Fin E→Bool) (base : Fin E→Y)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr) (Q : Y→Y→Prop)
    (hcover : ∀u v, Q u v ↔ ∃n, SameEdge (base n,base (successor hE n)) (u,v))
    (u v : Y×X) : HostAdjacent hE S base layers u v ↔ InputHost Q S base layers u v := by
  constructor
  · rintro ⟨e,he⟩
    cases e with
    | inl e =>
      rcases e with ⟨j,a,t⟩
      refine Or.inr ⟨j,?_,?_,a,t,map_sameEdge Prod.snd he⟩
      · rcases he with he | he
        · exact (congrArg (fun p => p.1.1) he).symm
        · exact (congrArg (fun p => p.2.1) he).symm
      · rcases he with he | he
        · exact (congrArg (fun p => p.2.1) he).symm
        · exact (congrArg (fun p => p.1.1) he).symm
    | inr e =>
      rcases e with ⟨n,x⟩
      refine Or.inl ⟨?_,(hcover _ _).mpr ⟨n,map_sameEdge Prod.fst he⟩⟩
      rcases he with he | he
      · exact (congrArg (fun p => p.1.2) he).symm.trans (congrArg (fun p => p.2.2) he)
      · exact (congrArg (fun p => p.2.2) he).symm.trans (congrArg (fun p => p.1.2) he)
  · intro hh
    rcases hh with ⟨hx,hq⟩ | ⟨j,hu,hv,a,t,he⟩
    · obtain ⟨n,hn⟩ := (hcover _ _).mp hq
      refine ⟨.inr (n,u.2),?_⟩
      change SameEdge ((base n,u.2),(base (successor hE n),u.2)) (u,v)
      rcases hn with hn | hn
      · apply Or.inl
        apply Prod.ext
        · exact Prod.ext (congrArg (fun p : Y×Y => p.1) hn) rfl
        · exact Prod.ext (congrArg (fun p : Y×Y => p.2) hn) hx
      · apply Or.inr
        apply Prod.ext
        · exact Prod.ext (congrArg (fun p : Y×Y => p.1) hn) hx
        · exact Prod.ext (congrArg (fun p : Y×Y => p.2) hn) rfl
    · refine ⟨.inl (j,a,t),?_⟩
      change SameEdge ((base (markIndex S j),(layers j).vertex (t,false)),
        (base (markIndex S j),choose (layers j) a ((layers j).vertex (t,false)))) (u,v)
      rcases he with he | he
      · exact Or.inl (Prod.ext (Prod.ext hu.symm (congrArg (fun p : X×X => p.1) he))
          (Prod.ext hv.symm (congrArg (fun p : X×X => p.2) he)))
      · exact Or.inr (Prod.ext (Prod.ext hv.symm (congrArg (fun p : X×X => p.1) he))
          (Prod.ext hu.symm (congrArg (fun p : X×X => p.2) he)))

/-- Actual displayed host partition, with ambient base adjacency supplied
by its own complete edge ledger rather than an output assumption. -/
theorem physical_partition (hE : 0<E) (h2 : 2≤r) (S : Fin E→Bool)
    (hzero : S ⟨0,hE⟩=true) (base : Fin E→Y)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (hq : 0<Profile.cardinality S)
    (hreturn : ∀color t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color))
    (hmarks : Function.Injective (fun j => base (markIndex S j)))
    (hbase : ∀n m, SameEdge (base n,base (successor hE n))
      (base m,base (successor hE m)) → n=m)
    (Q : Y→Y→Prop)
    (hcover : ∀u v, Q u v ↔ ∃n, SameEdge (base n,base (successor hE n)) (u,v)) :
    (∀u v, InputHost Q S base layers u v →
      ∃e, SameEdge (numericOutgoing hr S base C layers selectors hq e) (u,v)) ∧
    (∀e f, SameEdge (numericOutgoing hr S base C layers selectors hq e)
      (numericOutgoing hr S base C layers selectors hq f) → e=f) ∧
    (∀e, InputHost Q S base layers
      (numericOutgoing hr S base C layers selectors hq e).1
      (numericOutgoing hr S base C layers selectors hq e).2) := by
  have hp := numeric_partition hE h2 S hzero base C layers selectors hq hreturn hmarks hbase
  exact ⟨fun u v hh => hp.1 u v ((host_iff hE S base layers Q hcover u v).mpr hh),
    hp.2.1,fun e => (host_iff hE S base layers Q hcover _ _).mp (hp.2.2 e)⟩

variable {Label : Type}

/-- The assigned matching descriptors are the actual noncrossing forest
schedule, reindexed solely by the proved mark-cardinality equality. -/
def forestLayers (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (cycles : Label→CycleData X R χ r hr) (inside outside : NoncrossingWord.Forest Label)
    (hcard : Profile.cardinality S=(descriptors C cycles inside outside).length) :
    Fin (Profile.cardinality S)→CycleData X R χ r hr :=
  fun j => (descriptors C cycles inside outside)[(Fin.cast hcard j).val].1

def forestSelectors (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (cycles : Label→CycleData X R χ r hr) (inside outside : NoncrossingWord.Forest Label)
    (hcard : Profile.cardinality S=(descriptors C cycles inside outside).length) :
    Fin (Profile.cardinality S)→Bool :=
  fun j => (descriptors C cycles inside outside)[(Fin.cast hcard j).val].2

private theorem cast_word {q n : Nat} (h : q=n) (ds : List (CycleData X R χ r hr × Bool))
    (hn : n=ds.length) (color : Bool) :
    word (fun j : Fin q => ds[Fin.cast (h.trans hn) j |>.val].1)
      (fun j : Fin q => ds[Fin.cast (h.trans hn) j |>.val].2) color =
    word (fun j : Fin ds.length => ds[j.val].1)
      (fun j : Fin ds.length => ds[j.val].2) color := by
  subst n
  subst q
  rfl

/-- Input return is derived from actual nested passive matching cancellation
and the displayed active Hamilton cycle. No output return is postulated. -/
theorem forest_return (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (cycles : Label→CycleData X R χ r hr) (inside outside : NoncrossingWord.Forest Label)
    (hcard : Profile.cardinality S=(descriptors C cycles inside outside).length)
    (color : Bool) (t : Fin r) :
    applyWord (word (forestLayers S C cycles inside outside hcard)
      (forestSelectors S C cycles inside outside hcard) color) (C.vertex (t,color))=
      C.vertex (successor hr t,color) := by
  unfold forestLayers forestSelectors
  rw [cast_word hcard _ rfl color]
  exact descriptors_advance C cycles inside outside color t

/-- Complete physical edge partition for genuine nested matching data and
an actual base edge ledger. It has no output partition or return premise. -/
theorem forest_partition (hE : 0<E) (h2 : 2≤r) (S : Fin E→Bool)
    (hzero : S ⟨0,hE⟩=true) (base : Fin E→Y)
    (C : CycleData X R χ r hr) (cycles : Label→CycleData X R χ r hr)
    (inside outside : NoncrossingWord.Forest Label)
    (hcard : Profile.cardinality S=(descriptors C cycles inside outside).length)
    (hq : 0<Profile.cardinality S)
    (hmarks : Function.Injective (fun j => base (markIndex S j)))
    (hbase : ∀n m, SameEdge (base n,base (successor hE n))
      (base m,base (successor hE m)) → n=m)
    (Q : Y→Y→Prop)
    (hcover : ∀u v, Q u v ↔ ∃n, SameEdge (base n,base (successor hE n)) (u,v)) :
    let layers := forestLayers S C cycles inside outside hcard
    let selectors := forestSelectors S C cycles inside outside hcard
    (∀u v, InputHost Q S base layers u v →
      ∃e, SameEdge (numericOutgoing hr S base C layers selectors hq e) (u,v)) ∧
    (∀e f, SameEdge (numericOutgoing hr S base C layers selectors hq e)
      (numericOutgoing hr S base C layers selectors hq f) → e=f) ∧
    (∀e, InputHost Q S base layers
      (numericOutgoing hr S base C layers selectors hq e).1
      (numericOutgoing hr S base C layers selectors hq e).2) :=
  physical_partition hE h2 S hzero base C _ _ hq
    (forest_return S C cycles inside outside hcard) hmarks hbase Q hcover


/-- Actual simple physical AAC output tours with exact input-host edge
partition. Geometric hypotheses concern only the base Euler traversal. -/
theorem aac_decomposition (hE : 0<E) (h2 : 2≤r) (base : Fin E→Y)
    (baseColor : Fin E→Bool)
    (hcut : AACMarkIntervals.cyclicFlag hE baseColor ⟨0,hE⟩=true)
    (hmark : ∀n m, AACMarkIntervals.cyclicFlag hE baseColor n=true→base n=base m→n=m)
    (hcollision : ∀n m, base n=base m→n=m ∨ baseColor n≠baseColor m)
    (C : CycleData X R χ r hr) (cycles : Label→CycleData X R χ r hr)
    (inside outside : NoncrossingWord.Forest Label)
    (hcard : Profile.cardinality (AACMarkIntervals.cyclicFlag hE baseColor)=
      (descriptors C cycles inside outside).length)
    (hbase : ∀n m, SameEdge (base n,base (successor hE n))
      (base m,base (successor hE m)) → n=m)
    (Q : Y→Y→Prop)
    (hcover : ∀u v, Q u v ↔ ∃n, SameEdge (base n,base (successor hE n)) (u,v)) :
    let S := AACMarkIntervals.cyclicFlag hE baseColor
    let hq := AACFoldClock.cardinality_pos hE S hcut
    let layers := forestLayers S C cycles inside outside hcard
    let selectors := forestSelectors S C cycles inside outside hcard
    let tours := fun color => AACFoldClock.physical hE hr base baseColor C layers selectors color hq
    let hn := AACFoldClock.length_pos hr S hq
    (∀color, Function.Injective (tours color)) ∧
    (∀u v, InputHost Q S base layers u v → ∃color n,
      SameEdge (tours color n,tours color (successor hn n)) (u,v)) ∧
    (∀color n color' n', SameEdge (tours color n,tours color (successor hn n))
      (tours color' n',tours color' (successor hn n')) → color=color' ∧ n=n') ∧
    (∀color n, InputHost Q S base layers (tours color n) (tours color (successor hn n))) := by
  dsimp only
  let S := AACMarkIntervals.cyclicFlag hE baseColor
  let hq := AACFoldClock.cardinality_pos hE S hcut
  have hmarks : Function.Injective (fun j => base (markIndex S j)) := by
    intro j k he
    have hj := markIndex_spec S j
    have hk := markIndex_spec S k
    have hn := hmark _ _ hj.1 he
    apply Fin.ext
    rw [hn] at hj
    omega
  have hp := forest_partition hE h2 S hcut base C cycles inside outside hcard hq hmarks hbase Q hcover
  refine ⟨?_,?_,?_,?_⟩
  · intro color
    exact AACFoldClock.physical_injective hE hr base baseColor C _ _ color hq hcut hmark hcollision
  · intro u v hh
    obtain ⟨⟨color,n⟩,he⟩ := hp.1 u v hh
    exact ⟨color,n,he⟩
  · intro color n color' n' he
    have hh := hp.2.1 (color,n) (color',n') he
    exact ⟨congrArg (fun p : Bool × Fin (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length => p.1) hh,
      congrArg (fun p : Bool × Fin (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length => p.2) hh⟩
  · intro color n
    exact hp.2.2 (color,n)

#print axioms encode_injective
#print axioms encode_surjective
#print axioms decode_unique
#print axioms numeric_partition
#print axioms forest_return
#print axioms forest_partition
#print axioms aac_decomposition
end ErdePaths.AACFoldEdgeLedger
