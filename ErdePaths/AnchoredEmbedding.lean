import ErdePaths.ForkWiggle

namespace ErdePaths.AnchoredEmbedding
open SquareLift Wiggle SubdividedWiggle ForkWiggle

/-- Actual position i*s+k on the parent first-axis cycle. -/
def positionEncode {A s : Nat} (i : Fin A) (k : Fin s) : Fin (A*s) :=
  ⟨s*i.val+k.val,by
    have hi := Nat.mul_le_mul_right s (show i.val+1≤A by have := i.isLt; omega)
    rw [Nat.add_mul,Nat.mul_comm i.val] at hi
    have := k.isLt
    omega⟩

def positionDecode {A s : Nat} (hs : 0<s) (t : Fin (A*s)) : Fin A × Fin s :=
  (⟨t.val/s,Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using t.isLt)⟩,
   ⟨t.val%s,Nat.mod_lt _ hs⟩)

theorem positionDecode_encode {A s : Nat} (hs : 0<s) (i : Fin A) (k : Fin s) :
    positionDecode hs (positionEncode i k)=(i,k) := by
  apply Prod.ext <;> apply Fin.ext
  · simp only [positionDecode,positionEncode,Nat.mul_add_div hs,Nat.div_eq_of_lt k.isLt,Nat.add_zero]
  · simp only [positionDecode,positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt k.isLt]

theorem positionEncode_decode {A s : Nat} (hs : 0<s) (t : Fin (A*s)) :
    positionEncode (positionDecode hs t).1 (positionDecode hs t).2=t := by
  apply Fin.ext
  exact Nat.div_add_mod t.val s

theorem positionEncode_injective {A s : Nat} (hs : 0<s) :
    Function.Injective (fun p : Fin A × Fin s => positionEncode p.1 p.2) := by
  intro p q h
  have hh := congrArg (positionDecode hs) h
  simpa only [positionDecode_encode] using hh

/-- Bijection to ordinary fine rectangular coordinates. -/
def fineEncode {a B s : Nat} (v : FineVertex a B s) : Fin ((2*a)*s) × Fin B :=
  (positionEncode v.1.1 v.2,v.1.2)

def fineDecode {a B s : Nat} (hs : 0<s) (v : Fin ((2*a)*s) × Fin B) : FineVertex a B s :=
  (((positionDecode hs v.1).1,v.2),(positionDecode hs v.1).2)

theorem fineDecode_encode {a B s : Nat} (hs : 0<s) (v : FineVertex a B s) :
    fineDecode hs (fineEncode v)=v := by
  simp only [fineDecode,fineEncode,positionDecode_encode]

theorem fineEncode_decode {a B s : Nat} (hs : 0<s) (v : Fin ((2*a)*s) × Fin B) :
    fineEncode (fineDecode hs v)=v := by
  simp only [fineDecode,fineEncode,positionEncode_decode]

theorem fineEncode_injective {a B s : Nat} (hs : 0<s) : Function.Injective (@fineEncode a B s) := by
  intro u v h
  have hh := congrArg (fineDecode hs) h
  simpa only [fineDecode_encode] using hh

set_option linter.unusedSimpArgs false in
theorem fineEncode_next {a B s : Nat} (ha : 0<a) (hs : 0<s) (u : FineVertex a B s) :
    fineEncode (fineNext ha hs u)=
      (successor (Nat.mul_pos (show 0<2*a by omega) hs) (fineEncode u).1,(fineEncode u).2) := by
  have hi := u.1.1.isLt
  have hk := u.2.isLt
  have hb := Nat.mul_le_mul_right s (show u.1.1.val+1≤2*a by omega)
  rw [Nat.add_mul,Nat.mul_comm u.1.1.val] at hb
  by_cases hknext : u.2.val+1<s
  · apply Prod.ext
    · apply Fin.ext
      simp [fineEncode,positionEncode,fineNext,successor,hknext]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · simp [fineEncode,fineNext,hknext]
  · have hklast : u.2.val+1=s := by omega
    by_cases hinext : u.1.1.val+1<2*a
    · apply Prod.ext
      · apply Fin.ext
        simp [fineEncode,positionEncode,fineNext,successor,hknext,Nat.mod_eq_of_lt hinext]
        have hi' := Nat.mul_lt_mul_of_pos_right hinext hs
        rw [Nat.add_mul,Nat.mul_comm u.1.1.val] at hi'
        rw [Nat.mod_eq_of_lt (show s*u.1.1.val+u.2.val+1<(2*a)*s by omega),Nat.mul_add]
        omega
      · simp [fineEncode,fineNext,hknext]
    · have hilast : u.1.1.val+1=2*a := by omega
      apply Prod.ext
      · apply Fin.ext
        simp [fineEncode,positionEncode,fineNext,successor,hknext,hilast]
        have he : s*u.1.1.val+u.2.val+1=(2*a)*s := by
          have hh := congrArg (fun n => n*s) hilast
          rw [Nat.add_mul,Nat.mul_comm u.1.1.val] at hh
          omega
        simp [he]
      · simp [fineEncode,fineNext,hknext]

/-- Embedding in the actual product vertex type, using the supplied parent
cycle maps rather than an abstract graph isomorphism premise. -/
def embed {V W : Type} {a B s : Nat} (G : Fin ((2*a)*s) → V) (H : Fin B → W)
    (u : FineVertex a B s) : V × W := (G (fineEncode u).1,H (fineEncode u).2)

theorem embed_injective {V W : Type} {a B s : Nat} (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W) (hG : Function.Injective G) (hH : Function.Injective H) :
    Function.Injective (embed G H) := by
  intro u v h
  apply fineEncode_injective hs
  exact Prod.ext (hG (congrArg Prod.fst h)) (hH (congrArg Prod.snd h))

/-- Exact actual anchored host: all parent-G cycle edges at every H vertex,
and parent-H cycle edges only at the spaced G representatives i*s. -/
def AnchoredHost {V W : Type} {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W) (u v : V × W) : Prop :=
  (∃ t : Fin ((2*a)*s), ∃ j : Fin B,
    SameEdge ((G t,H j),(G (successor (Nat.mul_pos (show 0<2*a by omega) hs) t),H j)) (u,v)) ∨
  (∃ i : Fin (2*a), ∃ j : Fin B,
    SameEdge ((G (positionEncode i ⟨0,hs⟩),H j),
      (G (positionEncode i ⟨0,hs⟩),H (successor hB j))) (u,v))

theorem embed_next {V W : Type} {a B s : Nat} (ha : 0<a) (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W) (u : FineVertex a B s) :
    embed G H (fineNext ha hs u)=
      (G (successor (Nat.mul_pos (show 0<2*a by omega) hs) (fineEncode u).1),H (fineEncode u).2) := by
  simp only [embed,fineEncode_next]

theorem host_sameEdge {V W : Type} {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W) {e f : (V × W) × (V × W)}
    (he : AnchoredHost ha hB hs G H e.1 e.2) (h : SameEdge e f) : AnchoredHost ha hB hs G H f.1 f.2 := by
  rcases he with ⟨t,j,ht⟩ | ⟨i,j,hi⟩
  · exact Or.inl ⟨t,j,sameEdge_trans ht h⟩
  · exact Or.inr ⟨i,j,sameEdge_trans hi h⟩

theorem fine_to_host {V W : Type} {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W) {u v : FineVertex a B s}
    (h : FineAdjacent ha hB hs u v) : AnchoredHost ha hB hs G H (embed G H u) (embed G H v) := by
  rcases h with h | h | ⟨hu,hv,hx,hy|hy⟩
  · apply Or.inl
    refine ⟨(fineEncode u).1,(fineEncode u).2,Or.inl ?_⟩
    rw [←embed_next ha hs G H u,h]
    rfl
  · apply Or.inl
    refine ⟨(fineEncode v).1,(fineEncode v).2,Or.inr ?_⟩
    rw [←embed_next ha hs G H v,h]
    rfl
  · have u0 : u.2=(⟨0,hs⟩ : Fin s) := Fin.ext hu
    have v0 : v.2=(⟨0,hs⟩ : Fin s) := Fin.ext hv
    apply Or.inr
    refine ⟨u.1.1,u.1.2,Or.inl ?_⟩
    simp only [embed,fineEncode,u0,v0]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact congrArg (fun i => G (positionEncode i ⟨0,hs⟩)) hx
      · exact congrArg H hy
  · have u0 : u.2=(⟨0,hs⟩ : Fin s) := Fin.ext hu
    have v0 : v.2=(⟨0,hs⟩ : Fin s) := Fin.ext hv
    apply Or.inr
    refine ⟨v.1.1,v.1.2,Or.inr ?_⟩
    simp only [embed,fineEncode,u0,v0]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact congrArg (fun i => G (positionEncode i ⟨0,hs⟩)) hx.symm
      · exact congrArg H hy

/-- Every actual host edge has explicit fine endpoints; no host coverage
or decomposition statement is assumed. -/
theorem host_lift {V W : Type} {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W) {u v : V × W}
    (h : AnchoredHost ha hB hs G H u v) :
    ∃ p q : FineVertex a B s, embed G H p=u ∧ embed G H q=v ∧ FineAdjacent ha hB hs p q := by
  have transfer (p q : FineVertex a B s) (hpq : FineAdjacent ha hB hs p q)
      (he : SameEdge (embed G H p,embed G H q) (u,v)) :
      ∃ p q : FineVertex a B s, embed G H p=u ∧ embed G H q=v ∧ FineAdjacent ha hB hs p q := by
    rcases he with he | he
    · exact ⟨p,q,congrArg Prod.fst he,congrArg Prod.snd he,hpq⟩
    · exact ⟨q,p,congrArg Prod.snd he,congrArg Prod.fst he,fineAdjacent_symm ha hB hs hpq⟩
  rcases h with ⟨t,j,he⟩ | ⟨i,j,he⟩
  · let p : FineVertex a B s := fineDecode hs (t,j)
    have hp : embed G H p=(G t,H j) := by simp only [p,embed,fineEncode_decode]
    have hq : embed G H (fineNext ha hs p)=
        (G (successor (Nat.mul_pos (show 0<2*a by omega) hs) t),H j) := by
      rw [embed_next]
      simp only [p,fineEncode_decode]
    apply transfer p (fineNext ha hs p) (Or.inl rfl)
    simpa only [hp,hq] using he
  · let p : FineVertex a B s := representative hs (i,j)
    let q : FineVertex a B s := representative hs (i,successor hB j)
    apply transfer p q (Or.inr (Or.inr ⟨rfl,rfl,rfl,Or.inl rfl⟩))
    exact he

theorem host_to_fine {V W : Type} {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W) (hG : Function.Injective G) (hH : Function.Injective H)
    {u v : FineVertex a B s} (h : AnchoredHost ha hB hs G H (embed G H u) (embed G H v)) :
    FineAdjacent ha hB hs u v := by
  obtain ⟨p,q,hp,hq,hpq⟩ := host_lift ha hB hs G H h
  have he := embed_injective hs G H hG hH
  have pu := he hp
  have qv := he hq
  simpa only [pu,qv] using hpq

theorem exact_edge_correspondence {V W : Type} {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W) (hG : Function.Injective G) (hH : Function.Injective H)
    (u v : FineVertex a B s) :
    FineAdjacent ha hB hs u v ↔ AnchoredHost ha hB hs G H (embed G H u) (embed G H v) :=
  ⟨fine_to_host ha hB hs G H,host_to_fine ha hB hs G H hG hH⟩

/-- Injective maps reflect actual undirected endpoint equality. -/
theorem reflect_sameEdge {X Y : Type} (f : X → Y) (hf : Function.Injective f)
    {u v x y : X} (h : SameEdge (f u,f v) (f x,f y)) : SameEdge (u,v) (x,y) := by
  rcases h with h | h
  · exact Or.inl (Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h)))
  · exact Or.inr (Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h)))

/-- The two checked fine paths transported to actual vertices. Edge coverage
is obtained from the explicit host decoder, rather than required as input. -/
def anchoredPathDecomposition {V W : Type} {a B s : Nat}
    (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W)
    (hG : Function.Injective G) (hH : Function.Injective H) :
    GraphPathDecomposition (V × W)
      (AnchoredHost (by omega) (by omega) (by omega) G H) (cycleLength a B s) where
  Index := Bool
  indices := [false,true]
  vertices := fun p t => embed G H ((finePathDecomposition ha hB heven hs).vertices p t)
  simple := by
    intro p hp i j hij
    exact (finePathDecomposition ha hB heven hs).simple p hp
      (embed_injective (by omega) G H hG hH hij)
  adjacent := by
    intro p hp j
    exact fine_to_host (by omega) (by omega) (by omega) G H
      ((finePathDecomposition ha hB heven hs).adjacent p hp j)
  cover := by
    intro u v huv
    obtain ⟨x,y,hx,hy,hxy⟩ := host_lift (by omega) (by omega) (by omega) G H huv
    obtain ⟨p,hp,j,he⟩ := (finePathDecomposition ha hB heven hs).cover x y hxy
    refine ⟨p,hp,j,?_⟩
    have hh := map_sameEdge (embed G H) he
    simpa only [hx,hy,SameEdge,UndirectedEq] using hh
  unique := by
    intro p q hp hq j k he
    exact (finePathDecomposition ha hB heven hs).unique p q hp hq j k
      (reflect_sameEdge (embed G H) (embed_injective (by omega) G H hG hH) he)

/-- Exactly two paths, each of the balanced subdivided length. -/
def anchoredPathDecompositionExact {V W : Type} {a B s : Nat}
    (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W)
    (hG : Function.Injective G) (hH : Function.Injective H) :
    GraphPathDecomposition (V × W)
      (AnchoredHost (by omega) (by omega) (by omega) G H) ((2*a)*B*(s+1)/2) := by
  rw [←finePath_length a B s]
  exact anchoredPathDecomposition ha hB heven hs G H hG hH

theorem anchoredPathDecomposition_indices {V W : Type} {a B s : Nat}
    (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W)
    (hG : Function.Injective G) (hH : Function.Injective H) :
    (anchoredPathDecomposition ha hB heven hs G H hG hH).indices=[false,true] := rfl

/-- The ordinary Cartesian product edge relation on genuine vertex types. -/
def ProductRelation {V W : Type} (R : V → V → Prop) (S : W → W → Prop)
    (u v : V × W) : Prop := (u.2=v.2 ∧ R u.1 v.1) ∨ (u.1=v.1 ∧ S u.2 v.2)

theorem productRelation_symm {V W : Type} {R : V → V → Prop} {S : W → W → Prop}
    (hR : ∀ x y, R x y → R y x) (hS : ∀ x y, S x y → S y x)
    {u v : V × W} (h : ProductRelation R S u v) : ProductRelation R S v u := by
  rcases h with ⟨he,hr⟩ | ⟨he,hs⟩
  · exact Or.inl ⟨he.symm,hR _ _ hr⟩
  · exact Or.inr ⟨he.symm,hS _ _ hs⟩

/-- If the input maps are actual simple cycles in ambient graphs, every edge
of the anchored host is an actual Cartesian-product edge. -/
theorem host_in_product {V W : Type} {a B s : Nat}
    (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (G : Fin ((2*a)*s) → V) (H : Fin B → W)
    (R : V → V → Prop) (S : W → W → Prop)
    (hR : ∀ x y, R x y → R y x) (hS : ∀ x y, S x y → S y x)
    (hG : ∀ t, R (G t) (G (successor (Nat.mul_pos (show 0<2*a by omega) hs) t)))
    (hH : ∀ j, S (H j) (H (successor hB j)))
    {u v : V × W} (h : AnchoredHost ha hB hs G H u v) : ProductRelation R S u v := by
  have transfer (x y : V × W) (hxy : ProductRelation R S x y)
      (he : SameEdge (x,y) (u,v)) : ProductRelation R S u v := by
    rcases he with he | he
    · have hu : x=u := congrArg Prod.fst he
      have hv : y=v := congrArg Prod.snd he
      simpa only [hu,hv] using hxy
    · have hv : x=v := congrArg Prod.fst he
      have hu : y=u := congrArg Prod.snd he
      simpa only [hu,hv] using productRelation_symm hR hS hxy
  rcases h with ⟨t,j,he⟩ | ⟨i,j,he⟩
  · exact transfer (G t,H j) (G (successor (Nat.mul_pos (show 0<2*a by omega) hs) t),H j) (Or.inl ⟨rfl,hG t⟩) he
  · exact transfer (G (positionEncode i ⟨0,hs⟩),H j) (G (positionEncode i ⟨0,hs⟩),H (successor hB j)) (Or.inr ⟨rfl,hH j⟩) he

#print axioms anchoredPathDecompositionExact
#print axioms host_in_product
#print axioms exact_edge_correspondence
#print axioms host_lift
#print axioms embed_injective
#print axioms fineEncode_next
end ErdePaths.AnchoredEmbedding
