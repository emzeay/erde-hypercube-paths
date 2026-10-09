import ErdePaths.LayerOwnership

namespace ErdePaths.LayerPartition
open SquareLift PairedLayers NoncrossingWord LayerOwnership SubdividedWiggle
variable {X : Type} {R : X → X → Prop} {χ : X → Bool} {r q : Nat} {hr : 0<r}

/-- One common descriptor schedule, with complementary actual matchings. -/
def word (layers : Fin q → CycleData X R χ r hr) (selectors : Fin q → Bool)
    (color : Bool) : List (X → X) :=
  List.ofFn fun j => choose (layers j) (selectors j ^^ color)

theorem word_length (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) : (word layers selectors color).length=q := by
  simp [word]

theorem word_valid (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) : ValidWord χ (word layers selectors color) := by
  intro f hf
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
  exact ⟨choose_involutive _ _,choose_flips _ _⟩

def arrival (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) (t : Fin r) : X :=
  prefixApply (word layers selectors color) j.val (C.vertex (t,color))

def departure (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) (t : Fin r) : X :=
  choose (layers j) (selectors j ^^ color) (arrival C layers selectors color j t)

theorem arrival_side (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) (t : Fin r) :
    χ (arrival C layers selectors color j t)=flipN j.val color := by
  unfold arrival prefixApply
  rw [applyWord_side (valid_take (word_valid layers selectors color) j.val),C.bipartition]
  rw [List.length_take,word_length,Nat.min_eq_left (Nat.le_of_lt j.isLt)]

theorem arrival_injective (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) :
    Function.Injective (arrival C layers selectors color j) := by
  intro t z he
  have hp := applyWord_injective (valid_take (word_valid layers selectors color) j.val) he
  exact congrArg Prod.fst (vertex_injective C hp)

theorem arrival_covers_side (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) (x : X)
    (hx : χ x=flipN j.val color) : ∃ t, arrival C layers selectors color j t=x := by
  obtain ⟨u,hu⟩ := applyWord_surjective (valid_take (word_valid layers selectors color) j.val) x
  have hs := applyWord_side (valid_take (word_valid layers selectors color) j.val) u
  rw [hu,List.length_take,word_length,Nat.min_eq_left (Nat.le_of_lt j.isLt),hx] at hs
  have huc : χ u=color := flipN_injective j.val hs.symm
  have hcoord : (C.coordinate u).2=color := by
    have he := congrArg χ (C.vertex_coordinate u)
    rw [C.bipartition,huc] at he
    exact he
  refine ⟨(C.coordinate u).1,?_⟩
  have hv : C.vertex ((C.coordinate u).1,color)=u := by
    rw [←hcoord]
    exact C.vertex_coordinate u
  unfold arrival prefixApply
  rw [hv]
  exact hu

theorem departure_side (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) (t : Fin r) :
    χ (departure C layers selectors color j t)= !flipN j.val color := by
  change χ (choose (layers j) (selectors j ^^ color) (arrival C layers selectors color j t))=_
  rw [choose_flips (layers j),arrival_side C layers selectors color j t]

theorem departure_injective (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) :
    Function.Injective (departure C layers selectors color j) := by
  intro t z he
  apply arrival_injective C layers selectors color j
  have hh := congrArg (choose (layers j) (selectors j ^^ color)) he
  simpa only [departure,choose_involutive] using hh

theorem departure_covers_side (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) (x : X)
    (hx : χ x= !flipN j.val color) : ∃ t, departure C layers selectors color j t=x := by
  have hs : χ (choose (layers j) (selectors j ^^ color) x)=flipN j.val color := by
    rw [choose_flips (layers j),hx,Bool.not_not]
  obtain ⟨t,ht⟩ := arrival_covers_side C layers selectors color j _ hs
  exact ⟨t,by rw [departure,ht,choose_involutive]⟩

abbrev OutputLabel (q r : Nat) := Bool × Fin r × Fin q × Bool

def outputEdge (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (hq : 0<q) (e : OutputLabel q r) :
    (Fin q×X)×(Fin q×X) :=
  let y := arrival C layers selectors e.1 e.2.2.1 e.2.1
  let x := departure C layers selectors e.1 e.2.2.1 e.2.1
  if e.2.2.2 then ((e.2.2.1,x),(successor hq e.2.2.1,x))
    else ((e.2.2.1,y),(e.2.2.1,x))

def canonical (D : CycleData X R χ r hr) (a : Bool) (y : X) : X :=
  if χ y then choose D a y else y

theorem canonical_side (D : CycleData X R χ r hr) (a : Bool) (y : X) :
    χ (canonical D a y)=false := by
  unfold canonical
  cases h : χ y <;> simp [h,choose_flips]

theorem canonical_edge (D : CycleData X R χ r hr) (a : Bool) (y : X) :
    SameEdge (canonical D a y,choose D a (canonical D a y)) (y,choose D a y) := by
  unfold canonical
  cases h : χ y
  · exact Or.inl rfl
  · exact Or.inr (by simp only [↓reduceIte,choose_involutive])

/-- Output edges map to the shared host's literal canonical edge labels. -/
def encodeLabel (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (e : OutputLabel q r) : HostLabel q r :=
  let c := e.1
  let t := e.2.1
  let j := e.2.2.1
  let y := arrival C layers selectors c j t
  let x := departure C layers selectors c j t
  if e.2.2.2 then .inr (j,C.coordinate x)
    else .inl (j,selectors j ^^ c,(layers j).coordinate (canonical (layers j) (selectors j ^^ c) y) |>.fst)

private theorem coordinate_false (D : CycleData X R χ r hr) (x : X) (hx : χ x=false) :
    D.vertex ((D.coordinate x).1,false)=x := by
  have hs := congrArg χ (D.vertex_coordinate x)
  rw [D.bipartition,hx] at hs
  rw [←hs]
  exact D.vertex_coordinate x

theorem encodeLabel_decodes (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (hq : 0<q) (e : OutputLabel q r) :
    SameEdge (decode C layers hq (encodeLabel C layers selectors e)) (outputEdge C layers selectors hq e) := by
  rcases e with ⟨c,t,j,b⟩
  cases b
  · change SameEdge
      ((j,(layers j).vertex (((layers j).coordinate (canonical (layers j) (selectors j ^^ c)
        (arrival C layers selectors c j t))).1,false)),
       (j,choose (layers j) (selectors j ^^ c) ((layers j).vertex (((layers j).coordinate
        (canonical (layers j) (selectors j ^^ c) (arrival C layers selectors c j t))).1,false))))
      ((j,arrival C layers selectors c j t),(j,departure C layers selectors c j t))
    rw [coordinate_false _ _ (canonical_side _ _ _)]
    exact map_sameEdge (fun x => (j,x)) (canonical_edge _ _ _)
  · change SameEdge ((j,C.vertex (C.coordinate (departure C layers selectors c j t))),
      (successor hq j,C.vertex (C.coordinate (departure C layers selectors c j t))))
      ((j,departure C layers selectors c j t),(successor hq j,departure C layers selectors c j t))
    rw [C.vertex_coordinate]
    exact Or.inl rfl

private theorem canonical_injective_on_side (D : CycleData X R χ r hr) (a : Bool)
    (y z : X) (hs : χ y=χ z) (he : canonical D a y=canonical D a z) : y=z := by
  unfold canonical at he
  cases hy : χ y <;> rw [←hs,hy] at he
  · simpa only [Bool.false_eq_true,↓reduceIte] using he
  · have hh := congrArg (choose D a) he
    simpa only [↓reduceIte,choose_involutive] using hh

private theorem coordinate_first_injective_false (D : CycleData X R χ r hr)
    (y z : X) (hy : χ y=false) (hz : χ z=false)
    (he : (D.coordinate y).1=(D.coordinate z).1) : y=z := by
  have hh := congrArg (fun t => D.vertex (t,false)) he
  simpa only [coordinate_false D y hy,coordinate_false D z hz] using hh

/-- No two cyclic output-edge positions receive the same common-host label. -/
theorem encodeLabel_injective (C : CycleData X R χ r hr)
    (layers : Fin q → CycleData X R χ r hr) (selectors : Fin q → Bool) :
    Function.Injective (encodeLabel C layers selectors) := by
  intro e f he
  rcases e with ⟨c,t,j,b⟩
  rcases f with ⟨d,z,k,a⟩
  cases b <;> cases a
  · have hh := Sum.inl.inj he
    have hj : j=k := congrArg Prod.fst hh
    subst k
    have hsel : (selectors j ^^ c)=(selectors j ^^ d) := congrArg (fun p => p.2.1) hh
    have hc : c=d := by cases hjb : selectors j <;> cases c <;> cases d <;> simp_all
    subst d
    have hp := congrArg (fun p => p.2.2) hh
    have hz := coordinate_first_injective_false (layers j) _ _
      (canonical_side _ _ _) (canonical_side _ _ _) hp
    have harr := canonical_injective_on_side (layers j) (selectors j ^^ c) _ _
      ((arrival_side C layers selectors c j t).trans (arrival_side C layers selectors c j z).symm) hz
    have ht := arrival_injective C layers selectors c j harr
    subst z
    rfl
  · cases he
  · cases he
  · have hh := Sum.inr.inj he
    have hj : j=k := congrArg Prod.fst hh
    subst k
    have hp := congrArg Prod.snd hh
    have hx := congrArg C.vertex hp
    simp only [C.vertex_coordinate] at hx
    have hs := congrArg χ hx
    rw [departure_side C layers selectors c j t,departure_side C layers selectors d j z] at hs
    have hflip : flipN j.val c=flipN j.val d := by
      have hh := congrArg Bool.not hs
      simpa only [Bool.not_not] using hh
    have hc : c=d := flipN_injective j.val hflip
    subst d
    have ht := departure_injective C layers selectors c j hx
    subst z
    rfl

private theorem flipN_self (n : Nat) (b : Bool) : flipN n (flipN n b)=b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change flipN n (!(flipN n (!b)))=b
    rw [←flipN_not, Bool.not_not,ih]

/-- Every literal host label has an actual output position, with the color
forced by its vertical selector or horizontal physical bipartition. -/
theorem encodeLabel_surjective (C : CycleData X R χ r hr)
    (layers : Fin q → CycleData X R χ r hr) (selectors : Fin q → Bool) :
    Function.Surjective (encodeLabel C layers selectors) := by
  intro e
  cases e with
  | inl e =>
    rcases e with ⟨j,a,k⟩
    let c := a ^^ selectors j
    have hsel : (selectors j ^^ c)=a := by
      dsimp [c]
      cases a <;> cases selectors j <;> rfl
    let x0 := (layers j).vertex (k,false)
    let y := if flipN j.val c then choose (layers j) a x0 else x0
    have hy : χ y=flipN j.val c := by
      dsimp [y,x0]
      cases hp : flipN j.val c <;> simp [choose_flips,(layers j).bipartition]
    obtain ⟨t,ht⟩ := arrival_covers_side C layers selectors c j y hy
    have hz : canonical (layers j) a y=x0 := by
      unfold canonical
      rw [hy]
      dsimp [y]
      cases hp : flipN j.val c <;> simp [choose_involutive]
    refine ⟨(c,t,j,false),?_⟩
    change Sum.inl (j,selectors j ^^ c,((layers j).coordinate
      (canonical (layers j) (selectors j ^^ c) (arrival C layers selectors c j t))).1)=_
    rw [hsel,ht,hz]
    simp only [x0,(layers j).coordinate_vertex]
  | inr e =>
    rcases e with ⟨j,k,b⟩
    let x := C.vertex (k,b)
    let c := flipN j.val (!χ x)
    have hc : χ x= !flipN j.val c := by
      dsimp [c]
      rw [flipN_self,Bool.not_not]
    obtain ⟨t,ht⟩ := departure_covers_side C layers selectors c j x hc
    refine ⟨(c,t,j,true),?_⟩
    change Sum.inr (j,C.coordinate (departure C layers selectors c j t))=_
    rw [ht]
    simp only [x,C.coordinate_vertex]

/-- Exact edge partition for the two complementary scheduled prefix tours.
Their actual closing return and Hamilton packaging are supplied separately. -/
theorem output_edges_partition (h2 : 2≤r) (h4 : 4≤q)
    (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) :
    (∀ u v, HostAdjacent C layers (by omega) u v →
      ∃ e : OutputLabel q r, SameEdge (outputEdge C layers selectors (by omega) e) (u,v)) ∧
    (∀ e f : OutputLabel q r, SameEdge (outputEdge C layers selectors (by omega) e)
      (outputEdge C layers selectors (by omega) f) → e=f) := by
  constructor
  · intro u v hh
    obtain ⟨a,ha⟩ := hh
    obtain ⟨e,he⟩ := encodeLabel_surjective C layers selectors a
    refine ⟨e,?_⟩
    have hd := encodeLabel_decodes C layers selectors (by omega) e
    rw [he] at hd
    exact sameEdge_trans (sameEdge_symm hd) ha
  · intro e f he
    apply encodeLabel_injective C layers selectors
    apply decode_unique h2 h4 C layers
    exact sameEdge_trans (encodeLabel_decodes C layers selectors (by omega) e)
      (sameEdge_trans he (sameEdge_symm (encodeLabel_decodes C layers selectors (by omega) f)))

variable {Label : Type}

def descriptors (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) : List (CycleData X R χ r hr × Bool) :=
  (C,false) :: (inside.labels.map (fun a => (cycles a,false)) ++
    (C,true) :: outside.labels.map (fun a => (cycles a,false)))

private theorem descriptor_word (ds : List (CycleData X R χ r hr × Bool)) (color : Bool) :
    word (fun j : Fin ds.length => ds[j.val].1) (fun j : Fin ds.length => ds[j.val].2) color =
      ds.map (fun p => choose p.1 (p.2 ^^ color)) := by
  change List.ofFn ((fun p => choose p.1 (p.2 ^^ color)) ∘ (fun j : Fin ds.length => ds[j.val]))=_
  rw [←List.map_ofFn,List.ofFn_getElem]

theorem descriptors_word (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :
    word (fun j : Fin (descriptors C cycles inside outside).length => (descriptors C cycles inside outside)[j.val].1)
      (fun j : Fin (descriptors C cycles inside outside).length => (descriptors C cycles inside outside)[j.val].2) color =
        cycleWordColor C cycles inside outside color := by
  rw [descriptor_word]
  cases color <;> simp [descriptors,cycleWordColor,cycleWordZero,cycleWordOne,activeWord,
    List.map_map,Function.comp_def,choose]

/-- The full return is derived from the grammar on ONE common descriptor list. -/
theorem descriptors_advance (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) (t : Fin r) :
    applyWord (word
      (fun j : Fin (descriptors C cycles inside outside).length => (descriptors C cycles inside outside)[j.val].1)
      (fun j : Fin (descriptors C cycles inside outside).length => (descriptors C cycles inside outside)[j.val].2) color)
      (C.vertex (t,color))=C.vertex (successor hr t,color) := by
  rw [descriptors_word]
  exact LayerTour.forestWord_advance C cycles inside outside color t

/-- Common-coordinate tours avoid color-dependent layer types. -/
def commonTour (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (p : Fin r × Fin q × Bool) : Fin q×X :=
  (p.2.1,if p.2.2 then departure C layers selectors color p.2.1 p.1
    else arrival C layers selectors color p.2.1 p.1)

theorem commonTour_injective (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) : Function.Injective (commonTour C layers selectors color) := by
  intro p z he
  rcases p with ⟨t,j,b⟩
  rcases z with ⟨u,k,a⟩
  have hj : j=k := congrArg Prod.fst he
  subst k
  have hx := congrArg Prod.snd he
  cases b <;> cases a
  · have ht := arrival_injective C layers selectors color j hx
    change t=u at ht
    subst u; rfl
  · have hs := congrArg χ hx
    change χ (arrival C layers selectors color j t)=χ (departure C layers selectors color j u) at hs
    rw [arrival_side C layers selectors color j t,departure_side C layers selectors color j u] at hs
    cases hp : flipN j.val color <;> simp [hp] at hs
  · have hs := congrArg χ hx
    change χ (departure C layers selectors color j t)=χ (arrival C layers selectors color j u) at hs
    rw [departure_side C layers selectors color j t,arrival_side C layers selectors color j u] at hs
    cases hp : flipN j.val color <;> simp [hp] at hs
  · have ht := departure_injective C layers selectors color j hx
    change t=u at ht
    subst u; rfl

theorem commonTour_surjective (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) : Function.Surjective (commonTour C layers selectors color) := by
  rintro ⟨j,x⟩
  by_cases hx : χ x=flipN j.val color
  · obtain ⟨t,ht⟩ := arrival_covers_side C layers selectors color j x hx
    exact ⟨(t,j,false),Prod.ext rfl ht⟩
  · have hs : χ x= !flipN j.val color := by
      cases hh : χ x <;> cases hp : flipN j.val color <;> simp_all
    obtain ⟨t,ht⟩ := departure_covers_side C layers selectors color j x hs
    exact ⟨(t,j,true),Prod.ext rfl ht⟩

private theorem arrival_advance (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (j : Fin q) (t : Fin r) :
    prefixApply (word layers selectors color) (j.val+1) (C.vertex (t,color))=
      departure C layers selectors color j t := by
  have hj : j.val<(word layers selectors color).length := by rw [word_length]; exact j.isLt
  have hh := prefix_advance (r:=r) (⟨j.val,hj⟩ : Fin (word layers selectors color).length) (C.vertex (t,color))
  have hg : (word layers selectors color)[j.val]=choose (layers j) (selectors j ^^ color) := by
    exact List.getElem_ofFn (f:=fun j : Fin q => choose (layers j) (selectors j ^^ color))
      (show j.val<(List.ofFn fun j : Fin q => choose (layers j) (selectors j ^^ color)).length from by
        simpa only [List.length_ofFn] using j.isLt)
  rw [hg] at hh
  exact hh

/-- The ordered edge, including the outer seam, is exactly its output label. -/
theorem commonTour_step (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (hq : 0<q)
    (hreturn : ∀ t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color)) (p : Fin r × Fin q × Fin 2) :
    (commonTour C layers selectors color (LayerTour.flagCoordinates p),
      commonTour C layers selectors color (LayerTour.flagCoordinates (Wiggle.coordinateNext hr hq p)))=
      outputEdge C layers selectors hq (color,p.1,p.2.1,LayerTour.flagBool p.2.2) := by
  rcases p with ⟨t,j,b⟩
  by_cases hb : b.val=0
  · have he : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb
    subst b
    rfl
  · have he : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext (show b.val=1 from by have := b.isLt; omega)
    subst b
    by_cases hj : j.val+1<q
    · have hs : successor hq j=(⟨j.val+1,hj⟩ : Fin q) := Fin.ext (Nat.mod_eq_of_lt hj)
      have hx := arrival_advance C layers selectors color j t
      have hn : Wiggle.coordinateNext hr hq (t,j,(⟨1,by decide⟩ : Fin 2))=
          (t,⟨j.val+1,hj⟩,(⟨0,by decide⟩ : Fin 2)) := by simp [Wiggle.coordinateNext,hj]
      rw [hn]
      change ((j,departure C layers selectors color j t),
        (⟨j.val+1,hj⟩,arrival C layers selectors color ⟨j.val+1,hj⟩ t))=
          ((j,departure C layers selectors color j t),(successor hq j,departure C layers selectors color j t))
      rw [hs]
      exact Prod.ext rfl (Prod.ext rfl hx)
    · have hlast : j.val+1=q := by have := j.isLt; omega
      have hs : successor hq j=(⟨0,hq⟩ : Fin q) := by
        apply Fin.ext
        simp only [successor,hlast,Nat.mod_self]
      have hx := (arrival_advance C layers selectors color j t).symm
      rw [hlast] at hx
      have htq : (word layers selectors color).take q=word layers selectors color := by
        simpa only [word_length] using (List.take_length (l:=word layers selectors color))
      simp only [prefixApply,htq] at hx
      rw [hreturn] at hx
      have hn : Wiggle.coordinateNext hr hq (t,j,(⟨1,by decide⟩ : Fin 2))=
          (successor hr t,⟨0,hq⟩,(⟨0,by decide⟩ : Fin 2)) := by simp [Wiggle.coordinateNext,hj]
      rw [hn]
      change ((j,departure C layers selectors color j t),
        (⟨0,hq⟩,arrival C layers selectors color ⟨0,hq⟩ (successor hr t)))=
          ((j,departure C layers selectors color j t),(successor hq j,departure C layers selectors color j t))
      rw [hs]
      exact Prod.ext rfl (Prod.ext rfl (by simpa only [arrival,prefixApply,List.take_zero,applyWord] using hx.symm))

def scalarLabel (hq : 0<q) (p : Bool×Fin (r*(q*2))) : OutputLabel q r :=
  let u := LayerTour.flagCoordinates (Wiggle.indexCoordinates hq p.2)
  (p.1,u)

theorem scalarLabel_injective (hq : 0<q) : Function.Injective (@scalarLabel r q hq) := by
  intro p z he
  have hc := congrArg (fun e : OutputLabel q r => e.1) he
  change p.1=z.1 at hc
  have hi := Wiggle.indexCoordinates_injective hq
    (LayerTour.flagCoordinates_injective (congrArg Prod.snd he))
  exact Prod.ext hc hi

theorem scalarLabel_surjective (hq : 0<q) : Function.Surjective (@scalarLabel r q hq) := by
  rintro ⟨c,p⟩
  obtain ⟨u,hu⟩ := LayerTour.flagCoordinates_surjective p
  obtain ⟨i,hi⟩ := Wiggle.indexCoordinates_surjective hq u
  exact ⟨(c,i),by simp only [scalarLabel,hi,hu]⟩

def commonScalar (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (hq : 0<q) (i : Fin (r*(q*2))) : Fin q×X :=
  commonTour C layers selectors color (LayerTour.flagCoordinates (Wiggle.indexCoordinates hq i))

theorem commonScalar_injective (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (hq : 0<q) :
    Function.Injective (commonScalar C layers selectors color hq) := by
  intro i j he
  exact Wiggle.indexCoordinates_injective hq
    (LayerTour.flagCoordinates_injective (commonTour_injective C layers selectors color he))

theorem commonScalar_surjective (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (hq : 0<q) :
    Function.Surjective (commonScalar C layers selectors color hq) := by
  intro x
  obtain ⟨p,hp⟩ := commonTour_surjective C layers selectors color x
  obtain ⟨u,hu⟩ := LayerTour.flagCoordinates_surjective p
  obtain ⟨i,hi⟩ := Wiggle.indexCoordinates_surjective hq u
  exact ⟨i,by simp only [commonScalar,hi,hu,hp]⟩

theorem commonScalar_edge (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool) (color : Bool) (hq : 0<q)
    (hreturn : ∀ t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color)) (i : Fin (r*(q*2))) :
    (commonScalar C layers selectors color hq i,
      commonScalar C layers selectors color hq (successor (Nat.mul_pos hr (by omega)) i))=
        outputEdge C layers selectors hq (scalarLabel hq (color,i)) := by
  unfold commonScalar
  rw [Wiggle.indexCoordinates_next hr hq]
  exact commonTour_step C layers selectors color hq hreturn _

/-- Actual Hamilton factors and exact unique common-host edge ownership.
Only the return identity is an input here; noncrossing forests discharge it below. -/
theorem scheduled_decomposition (h2 : 2≤r) (h4 : 4≤q)
    (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (selectors : Fin q → Bool)
    (hreturn : ∀ color t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color)) :
    let hq : 0<q := by omega
    let tours := fun color => commonScalar C layers selectors color hq
    (∀ color, Function.Injective (tours color) ∧ Function.Surjective (tours color)) ∧
    (∀ color i, HostAdjacent C layers hq (tours color i)
      (tours color (successor (Nat.mul_pos hr (by omega)) i))) ∧
    (∀ u v, HostAdjacent C layers hq u v → ∃ color i,
      SameEdge (tours color i,tours color (successor (Nat.mul_pos hr (by omega)) i)) (u,v)) ∧
    (∀ color i color' i', SameEdge
      (tours color i,tours color (successor (Nat.mul_pos hr (by omega)) i))
      (tours color' i',tours color' (successor (Nat.mul_pos hr (by omega)) i')) → color=color' ∧ i=i') := by
  dsimp only
  obtain ⟨hcover,hunique⟩ := output_edges_partition h2 h4 C layers selectors
  refine ⟨fun color => ⟨commonScalar_injective C layers selectors color _,
    commonScalar_surjective C layers selectors color _⟩,?_,?_,?_⟩
  · intro color i
    refine ⟨encodeLabel C layers selectors (scalarLabel (by omega) (color,i)),?_⟩
    rw [commonScalar_edge C layers selectors color (by omega) (hreturn color)]
    exact encodeLabel_decodes C layers selectors (by omega) _
  · intro u v hh
    obtain ⟨e,he⟩ := hcover u v hh
    obtain ⟨⟨color,i⟩,hi⟩ := scalarLabel_surjective (r:=r) (by omega) e
    refine ⟨color,i,?_⟩
    rw [commonScalar_edge C layers selectors color (by omega) (hreturn color),hi]
    exact he
  · intro color i color' i' he
    rw [commonScalar_edge C layers selectors color (by omega) (hreturn color),
      commonScalar_edge C layers selectors color' (by omega) (hreturn color')] at he
    have hp := scalarLabel_injective (r:=r) (by omega) (hunique _ _ he)
    exact ⟨congrArg Prod.fst hp,congrArg Prod.snd hp⟩

/-- Unconditional local multilabel folding theorem: the common schedule is
constructed from the two forests, and its return is proved by cancellation. -/
theorem noncrossing_decomposition (h2 : 2≤r)
    (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (hpassive : 1≤inside.pairCount+outside.pairCount) :
    let ds := descriptors C cycles inside outside
    let layers := fun j : Fin ds.length => ds[j.val].1
    let selectors := fun j : Fin ds.length => ds[j.val].2
    ∃ hq : 0<ds.length,
      let tours := fun color => commonScalar C layers selectors color hq
      (∀ color, Function.Injective (tours color) ∧ Function.Surjective (tours color)) ∧
      (∀ color i, HostAdjacent C layers hq (tours color i)
        (tours color (successor (Nat.mul_pos hr (by omega)) i))) ∧
      (∀ u v, HostAdjacent C layers hq u v → ∃ color i,
        SameEdge (tours color i,tours color (successor (Nat.mul_pos hr (by omega)) i)) (u,v)) ∧
      (∀ color i color' i', SameEdge
        (tours color i,tours color (successor (Nat.mul_pos hr (by omega)) i))
        (tours color' i',tours color' (successor (Nat.mul_pos hr (by omega)) i')) → color=color' ∧ i=i') := by
  have hlen : (descriptors C cycles inside outside).length=2*(inside.pairCount+outside.pairCount+1) := by
    simp only [descriptors,List.length_cons,List.length_append,List.length_map,Forest.length_eq_twice_pairs]
    omega
  have h4 : 4≤(descriptors C cycles inside outside).length := by omega
  refine ⟨by omega,?_⟩
  exact scheduled_decomposition h2 h4 C _ _ (descriptors_advance C cycles inside outside)

#print axioms noncrossing_decomposition
#print axioms commonTour_step
#print axioms encodeLabel_decodes
#print axioms encodeLabel_injective
#print axioms output_edges_partition
#print axioms encodeLabel_surjective
end ErdePaths.LayerPartition
