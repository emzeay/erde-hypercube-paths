import ErdePaths.Conjecture
import ErdePaths.Binary
import ErdePaths.SquareLift
import ErdePaths.HallMarriage

/- Supplementary graph transfers, included in the default library build.
   This module depends on the core theorem; the core theorem does not depend on it.
   All matching inputs are checked graph factorizations, not path-existence inputs. -/
namespace ErdePaths.Consequences.ProductTransfer
open SquareLift

/-- A finite perfect-matching factorization. Each color is a bijective pairing
of all vertices; its edges partition the given undirected graph exactly once. -/
structure MatchingFactorization (V : Type) (R : V → V → Prop) (a : Nat) where
  Pair : Type
  pairs : List Pair
  complete : ∀ p, p ∈ pairs
  vertex : Fin a → Pair × Bool → V
  injective : ∀ c, Function.Injective (vertex c)
  surjective : ∀ c, Function.Surjective (vertex c)
  edge_iff : ∀ u v, R u v ↔ ∃ c p,
    SameEdge (vertex c (p,false), vertex c (p,true)) (u,v)
  color_unique : ∀ c d p q,
    SameEdge (vertex c (p,false),vertex c (p,true))
      (vertex d (q,false),vertex d (q,true)) → c=d

/-- Exactly one coordinate changes along an edge of its factor. -/
def CartesianAdjacent {t : Nat} {V : Fin t → Type}
    (R : ∀ i, V i → V i → Prop) (u v : ∀ i, V i) : Prop :=
  ∃ j, R j (u j) (v j) ∧ ∀ i, i≠j → u i=v i

def Uses {V : Type} (p : List V) (u v : V) : Prop :=
  (u,v) ∈ steps p ∨ (v,u) ∈ steps p

def Simple {V : Type} (R : V → V → Prop) (L : Nat) (p : List V) : Prop :=
  p.length=L+1 ∧ p.Nodup ∧ ∀ e ∈ steps p, R e.1 e.2

/-- Finite simple paths, with every undirected edge belonging to one index. -/
def HasPaths {V : Type} (R : V → V → Prop) (L : Nat) : Prop :=
  ∃ (I : Type) (indices : List I) (paths : I → List V),
    (∀ p ∈ indices, Simple R L (paths p)) ∧
    ∀ u v, R u v → ∃ p, p ∈ indices ∧ Uses (paths p) u v ∧
      ∀ q, q ∈ indices → Uses (paths q) u v → q=p

/-- Enumerate a finite dependent Cartesian product, without a new library. -/
def tuples : {t : Nat} → (P : Fin t → Type) → (∀ i, List (P i)) → List (∀ i, P i)
  | 0, _, _ => [fun i => Fin.elim0 i]
  | t+1, P, es => (es 0).flatMap fun x =>
      (tuples (fun i : Fin t => P i.succ) (fun i => es i.succ)).map
        (fun xs => Fin.cases x xs)

theorem tuples_complete {t : Nat} (P : Fin t → Type) (es : ∀ i, List (P i))
    (h : ∀ i x, x ∈ es i) (x : ∀ i, P i) : x ∈ tuples P es := by
  induction t with
  | zero =>
    have hx : x=(fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    simp [tuples,hx]
  | succ t ih =>
    have hx : Fin.cases (x 0) (fun i : Fin t => x i.succ)=x := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [←hx]
    exact List.mem_flatMap.mpr ⟨x 0,h 0 _,List.mem_map.mpr
      ⟨(fun i => x i.succ),ih _ _ (fun i => h i.succ) _,rfl⟩⟩

section Components
variable {t a : Nat} {V : Fin t → Type} {R : ∀ i, V i → V i → Prop}
variable (F : ∀ i, MatchingFactorization (V i) (R i) a)
abbrev Pairs := ∀ i, (F i).Pair

def embed (c : Fin a) (p : Pairs F) (x : Vertex t) : ∀ i, V i :=
  fun i => (F i).vertex c (p i,binaryTuple x i)

theorem embed_injective (c : Fin a) (p : Pairs F) : Function.Injective (embed F c p) := by
  intro x y h
  apply binaryTuple_injective
  funext i
  exact congrArg Prod.snd ((F i).injective c (congrFun h i))

theorem embed_eq (c : Fin a) (p q : Pairs F) (x y : Vertex t)
    (h : embed F c p x=embed F c q y) : p=q ∧ x=y := by
  have hi i := (F i).injective c (congrFun h i)
  refine ⟨funext (fun i => congrArg Prod.fst (hi i)),?_⟩
  apply binaryTuple_injective
  exact funext (fun i => congrArg Prod.snd (hi i))

theorem embed_adjacent (c : Fin a) (p : Pairs F) {x y : Vertex t}
    (h : Adjacent x y) : CartesianAdjacent R (embed F c p x) (embed F c p y) := by
  obtain ⟨j,hj,hi⟩ := h
  refine ⟨j,(F j).edge_iff _ _ |>.mpr ⟨c,p j,?_⟩,?_⟩
  · cases hx : binaryTuple x j <;> cases hy : binaryTuple y j
    · exact False.elim (hj (hx.trans hy.symm))
    · exact Or.inl (by simp [embed,hx,hy])
    · exact Or.inr (by simp [embed,hx,hy])
    · exact False.elim (hj (hx.trans hy.symm))
  · intro i hne
    simp only [embed,binaryTuple,hi i hne]

noncomputable def inverse (c : Fin a) (u : ∀ i, V i) (i : Fin t) : (F i).Pair × Bool :=
  Classical.choose ((F i).surjective c (u i))

theorem inverse_spec (c : Fin a) (u : ∀ i, V i) (i : Fin t) :
    (F i).vertex c (inverse F c u i)=u i := Classical.choose_spec ((F i).surjective c (u i))

noncomputable def unbits (b : Fin t → Bool) : Vertex t :=
  Classical.choose (binaryTuple_surjective b)

theorem unbits_spec (b : Fin t → Bool) : binaryTuple (unbits b)=b :=
  Classical.choose_spec (binaryTuple_surjective b)

/-- Every product edge lies in an actual cube component. -/
theorem edge_cover {u v : ∀ i, V i} (h : CartesianAdjacent R u v) :
    ∃ c p x y, Adjacent x y ∧ embed F c p x=u ∧ embed F c p y=v := by
  obtain ⟨j,hj,hi⟩ := h
  obtain ⟨c,z,hz⟩ := (F j).edge_iff _ _ |>.mp hj
  have hpair : ∀ i, (inverse F c u i).1=(inverse F c v i).1 := by
    intro i
    by_cases he : i=j
    · subst i
      rcases hz with hz | hz
      · have hu := (F j).injective c ((inverse_spec F c u j).trans (congrArg Prod.fst hz).symm)
        have hv := (F j).injective c ((inverse_spec F c v j).trans (congrArg Prod.snd hz).symm)
        exact (congrArg Prod.fst hu).trans (congrArg Prod.fst hv).symm
      · have hu := (F j).injective c ((inverse_spec F c u j).trans (congrArg Prod.snd hz).symm)
        have hv := (F j).injective c ((inverse_spec F c v j).trans (congrArg Prod.fst hz).symm)
        exact (congrArg Prod.fst hu).trans (congrArg Prod.fst hv).symm
    · exact congrArg Prod.fst ((F i).injective c
        ((inverse_spec F c u i).trans ((hi i he).trans (inverse_spec F c v i).symm)))
  let p : Pairs F := fun i => (inverse F c u i).1
  let x := unbits (fun i => (inverse F c u i).2)
  let y := unbits (fun i => (inverse F c v i).2)
  have hx : embed F c p x=u := by
    funext i
    simp only [embed,x,p,unbits_spec]
    exact inverse_spec F c u i
  have hy : embed F c p y=v := by
    funext i
    simp only [embed,y,p,unbits_spec,hpair i]
    exact inverse_spec F c v i
  refine ⟨c,p,x,y,⟨j,?_,?_⟩,hx,hy⟩
  · intro hb
    have huv : u j=v j := by
      rw [←congrFun hx j,←congrFun hy j]
      simp only [embed,binaryTuple,hb]
    have hne : u j≠v j := by
      intro he
      rcases hz with hz | hz
      · have hh := (F j).injective c
          ((congrArg Prod.fst hz).trans (he.trans (congrArg Prod.snd hz).symm))
        have := congrArg Prod.snd hh
        contradiction
      · have hh := (F j).injective c
          ((congrArg Prod.snd hz).trans (he.trans (congrArg Prod.fst hz).symm))
        have := congrArg Prod.snd hh
        contradiction
    exact hne huv
  · intro i hne
    have he := (F i).injective c
      ((inverse_spec F c u i).trans ((hi i hne).trans (inverse_spec F c v i).symm))
    change binaryTuple x i=binaryTuple y i
    simpa only [x,y,unbits_spec] using congrArg Prod.snd he

/-- Different colors or pair tuples cannot share a component edge. -/
theorem edge_unique (c d : Fin a) (p q : Pairs F) {x y z w : Vertex t}
    (hxy : Adjacent x y)
    (he : SameEdge (embed F c p x,embed F c p y) (embed F d q z,embed F d q w)) :
    c=d ∧ p=q ∧ SameEdge (x,y) (z,w) := by
  obtain ⟨j,hj,_⟩ := hxy
  have hc : c=d := by
    have hm : SameEdge ((F j).vertex c (p j,false),(F j).vertex c (p j,true))
        (embed F c p x j,embed F c p y j) := by
      cases hx : binaryTuple x j <;> cases hy : binaryTuple y j
      · exact False.elim (hj (hx.trans hy.symm))
      · exact Or.inl (by simp [embed,hx,hy])
      · exact Or.inr (by simp [embed,hx,hy])
      · exact False.elim (hj (hx.trans hy.symm))
    have he' : SameEdge (embed F c p x j,embed F c p y j)
        (embed F d q z j,embed F d q w j) := by
      rcases he with he | he
      · exact Or.inl (Prod.ext (congrFun (congrArg Prod.fst he) j) (congrFun (congrArg Prod.snd he) j))
      · exact Or.inr (Prod.ext (congrFun (congrArg Prod.fst he) j) (congrFun (congrArg Prod.snd he) j))
    have hz : binaryTuple z j≠binaryTuple w j := by
      intro hb
      have heq : embed F d q z j=embed F d q w j := by simp only [embed,hb]
      have heq' : embed F c p x j=embed F c p y j := by
        rcases he' with he' | he'
        · exact (congrArg Prod.fst he').trans (heq.trans (congrArg Prod.snd he').symm)
        · exact (congrArg Prod.fst he').trans (heq.symm.trans (congrArg Prod.snd he').symm)
      exact hj (congrArg Prod.snd ((F j).injective c heq'))
    have hn : SameEdge ((F j).vertex d (q j,false),(F j).vertex d (q j,true))
        (embed F d q z j,embed F d q w j) := by
      cases hb : binaryTuple z j <;> cases hb' : binaryTuple w j
      · exact False.elim (hz (hb.trans hb'.symm))
      · exact Or.inl (by simp [embed,hb,hb'])
      · exact Or.inr (by simp [embed,hb,hb'])
      · exact False.elim (hz (hb.trans hb'.symm))
    exact (F j).color_unique c d (p j) (q j)
      (sameEdge_trans hm (sameEdge_trans he' (sameEdge_symm hn)))
  subst d
  refine ⟨rfl,?_⟩
  rcases he with he | he
  · have h1 := embed_eq F c p q x z (congrArg Prod.fst he)
    have h2 := embed_eq F c p q y w (congrArg Prod.snd he)
    exact ⟨h1.1,Or.inl (Prod.ext h1.2 h2.2)⟩
  · have h1 := embed_eq F c p q x w (congrArg Prod.fst he)
    have h2 := embed_eq F c p q y z (congrArg Prod.snd he)
    exact ⟨h1.1,Or.inr (Prod.ext h1.2 h2.2)⟩

end Components

theorem steps_map {X Y : Type} (f : X → Y) (p : List X) :
    steps (p.map f)=(steps p).map (Prod.map f f) := by
  cases p with
  | nil => rfl
  | cons x xs => exact List.zip_map

theorem simple_map {X Y : Type} {S : X → X → Prop} {T : Y → Y → Prop}
    (f : X → Y) (hf : Function.Injective f) (hadj : ∀ x y, S x y → T (f x) (f y))
    {L : Nat} {p : List X} (hp : Simple S L p) : Simple T L (p.map f) := by
  refine ⟨by simpa using hp.1,?_,?_⟩
  · exact hp.2.1.map f (fun x y h he => h (hf he))
  · intro e he
    rw [steps_map] at he
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp he
    exact hadj z.1 z.2 (hp.2.2 z hz)

theorem uses_map {X Y : Type} (f : X → Y) {p : List X} {x y : X}
    (h : Uses p x y) : Uses (p.map f) (f x) (f y) := by
  rcases h with h | h
  · exact Or.inl (by rw [steps_map]; exact List.mem_map.mpr ⟨(x,y),h,rfl⟩)
  · exact Or.inr (by rw [steps_map]; exact List.mem_map.mpr ⟨(y,x),h,rfl⟩)

theorem uses_map_edge {X Y : Type} (f : X → Y) {p : List X} {u v : Y}
    (h : Uses (p.map f) u v) :
    ∃ x y, (x,y) ∈ steps p ∧ SameEdge (f x,f y) (u,v) := by
  rcases h with h | h
  · rw [steps_map] at h
    obtain ⟨⟨x,y⟩,hm,he⟩ := List.mem_map.mp h
    exact ⟨x,y,hm,Or.inl he⟩
  · rw [steps_map] at h
    obtain ⟨⟨x,y⟩,hm,he⟩ := List.mem_map.mp h
    exact ⟨x,y,hm,Or.inr he⟩

theorem uses_of_edge {X : Type} {p : List X} {x y u v : X}
    (h : (x,y) ∈ steps p) (he : SameEdge (x,y) (u,v)) : Uses p u v := by
  rcases he with he | he
  · exact Or.inl (he ▸ h)
  · exact Or.inr (he ▸ h)

section Transfer
variable {t a : Nat} {V : Fin t → Type} {R : ∀ i, V i → V i → Prop}
variable (F : ∀ i, MatchingFactorization (V i) (R i) a)

include F in
/-- The transfer itself works for every available cube path partition.
No bipartiteness, connectivity, girth, or Hamilton property is assumed. -/
theorem transfer {L : Nat} (h : HasPathDecomposition t L) :
    HasPaths (CartesianAdjacent R) L := by
  obtain ⟨I,is,paths,hpaths,hcover⟩ := h
  let ps := tuples (fun i => (F i).Pair) (fun i => (F i).pairs)
  have hpall (p : Pairs F) : p ∈ ps := tuples_complete _ _ (fun i => (F i).complete) p
  let indices : List (Fin a × Pairs F × I) := (List.ofFn id).flatMap fun c =>
    ps.flatMap fun p => is.map (fun i => (c,p,i))
  have hmem (c : Fin a) (p : Pairs F) (i : I) : (c,p,i) ∈ indices ↔ i ∈ is := by
    constructor
    · intro hm
      obtain ⟨d,_,hd⟩ := List.mem_flatMap.mp hm
      obtain ⟨q,_,hq⟩ := List.mem_flatMap.mp hd
      obtain ⟨j,hj,he⟩ := List.mem_map.mp hq
      have hh : j=i := congrArg (fun z : Fin a × Pairs F × I => z.2.2) he
      exact hh ▸ hj
    · intro hi
      exact List.mem_flatMap.mpr ⟨c,by simp [List.mem_ofFn],
        List.mem_flatMap.mpr ⟨p,hpall p,List.mem_map.mpr ⟨i,hi,rfl⟩⟩⟩
  refine ⟨Fin a × Pairs F × I,indices,
    (fun q => (paths q.2.2).map (embed F q.1 q.2.1)),?_,?_⟩
  · rintro ⟨c,p,i⟩ hi
    exact simple_map (embed F c p) (embed_injective F c p)
      (fun _ _ => embed_adjacent F c p) (hpaths i ((hmem c p i).mp hi))
  · intro u v huv
    obtain ⟨c,p,x,y,hxy,hx,hy⟩ := edge_cover F huv
    obtain ⟨i,hi,he,huniq⟩ := hcover x y hxy
    refine ⟨(c,p,i),(hmem c p i).mpr hi,?_,?_⟩
    · have hm := uses_map (embed F c p) he
      simpa only [hx,hy] using hm
    · rintro ⟨d,q,j⟩ hj he'
      have hj' := (hmem d q j).mp hj
      obtain ⟨z,w,hzw,hout⟩ := uses_map_edge (embed F d q) he'
      have hzadj := (hpaths j hj').2.2 (z,w) hzw
      have hout' : SameEdge (embed F d q z,embed F d q w)
          (embed F c p x,embed F c p y) := by simpa only [hx,hy] using hout
      obtain ⟨hd,hq,hexy⟩ := edge_unique F d c q p hzadj hout'
      have hjx : UsesEdge (paths j) x y := uses_of_edge hzw hexy
      have hji := huniq j hj' hjx
      exact Prod.ext hd (Prod.ext hq hji)

include F in
/-- Equal-length path transfer from the proved even-cube theorem. -/
theorem paths (L : Nat) (ht : 2≤t) (heven : t%2=0) (hL : 1≤L)
    (hlt : L<2^t) (hdiv : L∣t*2^(t-1)) : HasPaths (CartesianAdjacent R) L :=
  transfer F (Conjecture.paths t L ht heven hL hlt hdiv)

/-- Six arbitrary graphs with eight perfect matching factors each admit
a partition of their Cartesian product into simple 48-edge paths. For
8-regular bipartite factors, Hall's theorem supplies the input factorization. -/
theorem six_eight_regular {V : Fin 6 → Type} {R : ∀ i, V i → V i → Prop}
    (F : ∀ i, MatchingFactorization (V i) (R i) 8) :
    HasPaths (CartesianAdjacent R) 48 :=
  paths F 48 (by decide) (by decide) (by decide) (by decide) (by decide)

end Transfer

/-- Explicit three-matchings construction for K₄. No matching-existence
theorem or unverified certificate is needed for this specialization. -/
def k4Vertex (c : Fin 3) (p : Fin 2 × Bool) : Fin 4 :=
  match c.val,p.1.val,p.2 with
  | 0,0,false => 0 | 0,0,true => 1
  | 0,_,false => 2 | 0,_,true => 3
  | 1,0,false => 0 | 1,0,true => 2
  | 1,_,false => 1 | 1,_,true => 3
  | _,0,false => 0 | _,0,true => 3
  | _,_,false => 1 | _,_,true => 2

def k4Factorization : MatchingFactorization (Fin 4) (fun u v => u≠v) 3 where
  Pair := Fin 2
  pairs := List.ofFn id
  complete := fun p => List.mem_ofFn.mpr ⟨p,rfl⟩
  vertex := k4Vertex
  injective := by
    have h : ∀ (c : Fin 3) (p q : Fin 2) (b d : Bool),
        k4Vertex c (p,b)=k4Vertex c (q,d) → p=q ∧ b=d := by decide
    rintro c ⟨p,b⟩ ⟨q,d⟩ he
    exact Prod.ext (h c p q b d he).1 (h c p q b d he).2
  surjective := by
    have h : ∀ (c : Fin 3) (x : Fin 4), ∃ p : Fin 2, ∃ b : Bool,
        k4Vertex c (p,b)=x := by decide
    intro c x
    obtain ⟨p,b,hb⟩ := h c x
    exact ⟨(p,b),hb⟩
  edge_iff := by unfold SameEdge; decide
  color_unique := by unfold SameEdge; decide

/-- Literal Hamming graph: exactly one of the t four-letter coordinates differs. -/
def Hamming4Adjacent {t : Nat} (u v : Fin t → Fin 4) : Prop :=
  ∃ j, u j≠v j ∧ ∀ i, i≠j → u i=v i

/-- A fully instantiated nonbinary Hamming-graph consequence, uniformly in
every even dimension t, with no factorization hypotheses remaining. -/
theorem hamming4_paths (t L : Nat) (ht : 2≤t) (heven : t%2=0) (hL : 1≤L)
    (hlt : L<2^t) (hdiv : L∣t*2^(t-1)) : HasPaths (@Hamming4Adjacent t) L :=
  paths (fun _ : Fin t => k4Factorization) L ht heven hL hlt hdiv

theorem hamming4_six : HasPaths (@Hamming4Adjacent 6) 48 :=
  hamming4_paths 6 48 (by decide) (by decide) (by decide) (by decide) (by decide)

namespace Bipartite
open HallColor

/-- The simple graph represented by the original bipartite edge list. -/
def Adj {N : Nat} (G : HallColor.Bipartite N N) (u v : Fin N × Bool) : Prop :=
  ∃ e ∈ G.edges, SameEdge ((G.left e,false),(G.right e,true)) (u,v)

/-- No two distinct listed edges have the same endpoint pair. -/
def Simple {N : Nat} (G : HallColor.Bipartite N N) : Prop :=
  ∀ e ∈ G.edges, ∀ f ∈ G.edges,
    G.left e=G.left f → G.right e=G.right f → e=f

private theorem count_one_unique {E : Type} (es : List E) (p : E → Bool)
    (h : es.countP p=1) {e f : E} (he : e ∈ es) (hpe : p e=true)
    (hf : f ∈ es) (hpf : p f=true) : e=f := by
  have he' := List.mem_filter.mpr ⟨he,hpe⟩
  have hf' := List.mem_filter.mpr ⟨hf,hpf⟩
  rw [List.countP_eq_length_filter] at h
  cases hh : es.filter p with
  | nil => simp [hh] at h
  | cons z zs =>
    have hz : zs=[] := by
      have hl : zs.length=0 := by simp only [hh,List.length_cons] at h; omega
      exact List.length_eq_zero_iff.mp hl
    simp only [hh,hz,List.mem_cons,List.not_mem_nil,or_false] at he' hf'
    exact he'.trans hf'.symm

section Coloring
variable {N a : Nat} (G : HallColor.Bipartite N N)
variable (color : G.Edge → Nat) (hc : G.Labeling a color)

include hc in
private theorem exists_left (c : Fin a) (x : Fin N) :
    ∃ e ∈ G.edges, G.left e=x ∧ color e=c.val := by
  have hp : 0<G.edges.countP (fun e => decide (G.left e=x ∧ color e=c.val)) := by
    rw [hc.2.1 x c]; decide
  obtain ⟨e,he,hp⟩ := List.countP_pos_iff.mp hp
  exact ⟨e,he,of_decide_eq_true hp⟩

noncomputable def edge (c : Fin a) (x : Fin N) : G.Edge :=
  Classical.choose (exists_left G color hc c x)

theorem edge_spec (c : Fin a) (x : Fin N) :
    edge G color hc c x ∈ G.edges ∧
      G.left (edge G color hc c x)=x ∧ color (edge G color hc c x)=c.val :=
  Classical.choose_spec (exists_left G color hc c x)

theorem edge_eq (c : Fin a) {e : G.Edge} (he : e ∈ G.edges)
    (hcolor : color e=c.val) : edge G color hc c (G.left e)=e := by
  have hs := edge_spec G color hc c (G.left e)
  exact count_one_unique G.edges _ (hc.2.1 (G.left e) c) hs.1
    (by simp [hs.2]) he (by simp [hcolor])

noncomputable def mate (c : Fin a) (x : Fin N) : Fin N := G.right (edge G color hc c x)

theorem mate_injective (c : Fin a) : Function.Injective (mate G color hc c) := by
  intro x y he
  have hx := edge_spec G color hc c x
  have hy := edge_spec G color hc c y
  have hh := count_one_unique G.edges _ (hc.2.2 (mate G color hc c x) c)
    hx.1 (by simp [mate,hx.2.2]) hy.1 (by apply decide_eq_true; exact ⟨he.symm,hy.2.2⟩)
  exact hx.2.1.symm.trans ((congrArg G.left hh).trans hy.2.1)

theorem mate_surjective (c : Fin a) : Function.Surjective (mate G color hc c) := by
  intro y
  have hp : 0<G.edges.countP (fun e => decide (G.right e=y ∧ color e=c.val)) := by
    rw [hc.2.2 y c]; decide
  obtain ⟨e,he,hp⟩ := List.countP_pos_iff.mp hp
  have he' := of_decide_eq_true hp
  exact ⟨G.left e,by rw [mate,edge_eq G color hc c he he'.2]; exact he'.1⟩

noncomputable def pairedVertex (c : Fin a) (p : Fin N × Bool) : Fin N × Bool :=
  if p.2 then (mate G color hc c p.1,true) else (p.1,false)

theorem pairedVertex_injective (c : Fin a) : Function.Injective (pairedVertex G color hc c) := by
  rintro ⟨x,b⟩ ⟨y,d⟩ he
  cases b <;> cases d <;> simp only [pairedVertex,Bool.false_eq_true,ite_false,ite_true,Prod.mk.injEq] at he ⊢
  · exact he
  · exact False.elim he.2
  · exact False.elim (Bool.noConfusion he.2)
  · exact ⟨mate_injective G color hc c he.1,True.intro⟩

theorem pairedVertex_surjective (c : Fin a) : Function.Surjective (pairedVertex G color hc c) := by
  rintro ⟨x,b⟩
  cases b
  · exact ⟨(x,false),rfl⟩
  · obtain ⟨y,hy⟩ := mate_surjective G color hc c x
    exact ⟨(y,true),by simp only [pairedVertex,ite_true,hy]⟩

include hc in
/-- Hall's checked edge coloring yields actual bijective perfect matchings. -/
noncomputable def ofLabeling (hSimple : Simple G) :
    MatchingFactorization (Fin N × Bool) (Adj G) a where
  Pair := Fin N
  pairs := List.finRange N
  complete := List.mem_finRange
  vertex := pairedVertex G color hc
  injective := pairedVertex_injective G color hc
  surjective := pairedVertex_surjective G color hc
  edge_iff := by
    intro u v
    constructor
    · rintro ⟨e,he,hout⟩
      let c : Fin a := ⟨color e,hc.1 e he⟩
      refine ⟨c,G.left e,?_⟩
      simpa only [pairedVertex,Bool.false_eq_true,ite_false,ite_true,mate,edge_eq G color hc c he rfl] using hout
    · rintro ⟨c,x,hout⟩
      have hs := edge_spec G color hc c x
      refine ⟨edge G color hc c x,hs.1,?_⟩
      simpa only [pairedVertex,Bool.false_eq_true,ite_false,ite_true,mate,hs.2.1] using hout
  color_unique := by
    intro c d x y he
    have hx := edge_spec G color hc c x
    have hy := edge_spec G color hc d y
    rcases he with he | he
    · have hl : x=y := congrArg (fun z : (Fin N × Bool) × (Fin N × Bool) => z.1.1) he
      have hr : mate G color hc c x=mate G color hc d y :=
        congrArg (fun z : (Fin N × Bool) × (Fin N × Bool) => z.2.1) he
      have hh := hSimple _ hx.1 _ hy.1 (hx.2.1.trans (hl.trans hy.2.1.symm)) hr
      exact Fin.ext (hx.2.2.symm.trans ((congrArg color hh).trans hy.2.2))
    · have hh : false=true :=
        congrArg (fun z : (Fin N × Bool) × (Fin N × Bool) => z.1.2) he
      contradiction

end Coloring

/-- Every finite simple regular bipartite graph (in the project's faithful
edge-list representation) has the required matching factorization. -/
noncomputable def ofRegular {N a : Nat} (G : HallColor.Bipartite N N)
    (hSimple : Simple G) (hRegular : G.Regular a) :
    MatchingFactorization (Fin N × Bool) (Adj G) a :=
  ofLabeling G (Classical.choose (HallMarriage.regular_labeling a G hRegular))
    (Classical.choose_spec (HallMarriage.regular_labeling a G hRegular)) hSimple

end Bipartite

/-- Full regular-bipartite specialization: matchings are constructed internally
using the existing formal Hall theorem. Different factors may have different orders. -/
theorem regular_bipartite_paths {t a : Nat} {N : Fin t → Nat}
    (G : ∀ i, HallColor.Bipartite (N i) (N i))
    (hSimple : ∀ i, Bipartite.Simple (G i)) (hRegular : ∀ i, (G i).Regular a)
    (L : Nat) (ht : 2≤t) (heven : t%2=0) (hL : 1≤L)
    (hlt : L<2^t) (hdiv : L∣t*2^(t-1)) :
    HasPaths (CartesianAdjacent (fun i => Bipartite.Adj (G i))) L :=
  paths (fun i => Bipartite.ofRegular (G i) (hSimple i) (hRegular i)) L ht heven hL hlt hdiv

theorem regular_bipartite_six_eight {N : Fin 6 → Nat}
    (G : ∀ i, HallColor.Bipartite (N i) (N i))
    (hSimple : ∀ i, Bipartite.Simple (G i)) (hRegular : ∀ i, (G i).Regular 8) :
    HasPaths (CartesianAdjacent (fun i => Bipartite.Adj (G i))) 48 :=
  regular_bipartite_paths G hSimple hRegular 48
    (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms transfer
#print axioms paths
#print axioms six_eight_regular
#print axioms k4Factorization
#print axioms hamming4_paths
#print axioms hamming4_six
#print axioms Bipartite.ofRegular
#print axioms regular_bipartite_paths
#print axioms regular_bipartite_six_eight

namespace RoundRobin
private theorem mod_cases {n x : Nat} (_hn : 0<n) (hx : x<2*n) :
    x%n=x ∨ x%n+n=x := by
  by_cases h : x<n
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · have hh : x%n=(x-n)%n := Nat.mod_eq_sub_mod (by omega)
    have hs : (x-n)%n=x-n := Nat.mod_eq_of_lt (by omega)
    rw [hs] at hh
    exact Or.inr (by omega)

private theorem double_inj (m : Nat) (c d : Fin (2*m+1))
    (h : (2*c.val)%(2*m+1)=(2*d.val)%(2*m+1)) : c=d := by
  have hc := c.isLt
  have hd := d.isLt
  have h1 := mod_cases (n:=2*m+1) (x:=2*c.val) (by omega) (by omega)
  have h2 := mod_cases (n:=2*m+1) (x:=2*d.val) (by omega) (by omega)
  apply Fin.ext
  omega

def rotate (m : Nat) (c : Fin (2*m+1)) (x : Fin (2*m+2)) : Fin (2*m+2) :=
  if x.val=2*m+1 then x else
    ⟨(c.val+x.val)%(2*m+1), Nat.lt_trans (Nat.mod_lt _ (by omega)) (by omega)⟩

private theorem rotate_val (m : Nat) (c : Fin (2*m+1)) (x : Fin (2*m+2)) :
    (rotate m c x).val=if x.val=2*m+1 then x.val else (c.val+x.val)%(2*m+1) := by
  by_cases h : x.val=2*m+1 <;> simp [rotate,h]

private theorem rotate_inj (m : Nat) (c : Fin (2*m+1)) : Function.Injective (rotate m c) := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have hc := c.isLt
  have hv := congrArg Fin.val h
  rw [rotate_val,rotate_val] at hv
  split at hv <;> split at hv
  · exact Fin.ext (by omega)
  · have hz := Nat.mod_lt (c.val+y.val) (by omega : 0<2*m+1); omega
  · have hz := Nat.mod_lt (c.val+x.val) (by omega : 0<2*m+1); omega
  · have h1 := mod_cases (n:=2*m+1) (x:=c.val+x.val) (by omega) (by omega)
    have h2 := mod_cases (n:=2*m+1) (x:=c.val+y.val) (by omega) (by omega)
    exact Fin.ext (by omega)

private theorem rotate_surj (m : Nat) (c : Fin (2*m+1)) : Function.Surjective (rotate m c) := by
  intro y
  by_cases hy : y.val=2*m+1
  · exact ⟨y,by simp [rotate,hy]⟩
  · let x : Fin (2*m+2) := ⟨(y.val+(2*m+1)-c.val)%(2*m+1),
      Nat.lt_trans (Nat.mod_lt _ (by omega)) (by omega)⟩
    refine ⟨x,Fin.ext ?_⟩
    have hc := c.isLt
    have hyl := y.isLt
    have hxl : x.val<2*m+1 := Nat.mod_lt _ (by omega)
    simp only [rotate,show x.val≠2*m+1 by omega,ite_false,Fin.val_mk]
    have h1 := mod_cases (n:=2*m+1) (x:=y.val+(2*m+1)-c.val) (by omega) (by omega)
    have h2 := mod_cases (n:=2*m+1) (x:=c.val+x.val) (by omega) (by omega)
    change (c.val+(y.val+(2*m+1)-c.val)%(2*m+1))%(2*m+1)=c.val+(y.val+(2*m+1)-c.val)%(2*m+1) ∨
      (c.val+(y.val+(2*m+1)-c.val)%(2*m+1))%(2*m+1)+(2*m+1)=
      c.val+(y.val+(2*m+1)-c.val)%(2*m+1) at h2
    change (y.val+(2*m+1)-c.val)%(2*m+1)<2*m+1 at hxl
    change (c.val+(y.val+(2*m+1)-c.val)%(2*m+1))%(2*m+1)=y.val
    have hfinal := Nat.mod_lt (c.val+(y.val+(2*m+1)-c.val)%(2*m+1)) (by omega : 0<2*m+1)
    have hraw : y.val+(2*m+1)-c.val+c.val=y.val+(2*m+1) := by omega
    omega

def base (m : Nat) (p : Fin (m+1) × Bool) : Fin (2*m+2) :=
  ⟨if p.2 then 2*m+1-p.1.val else p.1.val, by have := p.1.isLt; cases p.2 <;> simp <;> omega⟩

private theorem base_inj (m : Nat) : Function.Injective (base m) := by
  rintro ⟨p,b⟩ ⟨q,d⟩ h
  have hp := p.isLt
  have hq := q.isLt
  have hv := congrArg Fin.val h
  change (if b then 2*m+1-p.val else p.val)=(if d then 2*m+1-q.val else q.val) at hv
  cases b <;> cases d <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hv
  · exact Prod.ext (Fin.ext hv) rfl
  · omega
  · omega
  · have hpq : p=q := Fin.ext (by omega)
    exact Prod.ext hpq rfl

private theorem base_surj (m : Nat) : Function.Surjective (base m) := by
  intro x
  by_cases hx : x.val<m+1
  · exact ⟨(⟨x.val,hx⟩,false),Fin.ext rfl⟩
  · have hxl := x.isLt
    exact ⟨(⟨2*m+1-x.val,by omega⟩,true),Fin.ext (by simp [base]; omega)⟩


def vertex (m : Nat) (c : Fin (2*m+1)) (p : Fin (m+1) × Bool) :=
  rotate m c (base m p)

private theorem double_surj (m : Nat) (z : Fin (2*m+1)) :
    ∃ c : Fin (2*m+1), (2*c.val)%(2*m+1)=z.val := by
  have hz := z.isLt
  by_cases h : z.val%2=0
  · let c : Fin (2*m+1) := ⟨z.val/2,by omega⟩
    refine ⟨c,?_⟩
    have he : 2*c.val=z.val := by dsimp [c]; omega
    rw [he,Nat.mod_eq_of_lt hz]
  · have ho : (z.val+(2*m+1))%2=0 := by
      rw [Nat.add_mod]; omega
    let c : Fin (2*m+1) := ⟨(z.val+(2*m+1))/2,by omega⟩
    refine ⟨c,?_⟩
    have he : 2*c.val=z.val+(2*m+1) := by dsimp [c]; omega
    rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hz]

def Color (m : Nat) (c : Fin (2*m+1)) (u v : Fin (2*m+2)) : Prop :=
  (u.val=2*m+1 ∧ v.val=c.val) ∨ (v.val=2*m+1 ∧ u.val=c.val) ∨
  (u.val<2*m+1 ∧ v.val<2*m+1 ∧ (u.val+v.val)%(2*m+1)=(2*c.val)%(2*m+1))

private theorem color_vertex (m : Nat) (c : Fin (2*m+1)) (p : Fin (m+1)) :
    Color m c (vertex m c (p,false)) (vertex m c (p,true)) := by
  have hp := p.isLt
  have hc := c.isLt
  have h0 : (base m (p,false)).val=p.val := rfl
  have h1 : (base m (p,true)).val=2*m+1-p.val := rfl
  have hv0 := rotate_val m c (base m (p,false))
  have hv1 := rotate_val m c (base m (p,true))
  rw [h0] at hv0
  rw [h1] at hv1
  by_cases hz : p.val=0
  · have hu : (vertex m c (p,false)).val=c.val := by
      change (rotate m c (base m (p,false))).val=c.val
      rw [hv0]; simp [hz,Nat.mod_eq_of_lt hc]
    have hv : (vertex m c (p,true)).val=2*m+1 := by
      change (rotate m c (base m (p,true))).val=2*m+1
      rw [hv1]; simp [hz]
    exact Or.inr (Or.inl ⟨hv,hu⟩)
  · have hb0 : p.val≠2*m+1 := by omega
    have hb1 : 2*m+1-p.val≠2*m+1 := by omega
    simp only [hb0,hb1,ite_false] at hv0 hv1
    have hu : (vertex m c (p,false)).val=(c.val+p.val)%(2*m+1) := hv0
    have hv : (vertex m c (p,true)).val=(c.val+(2*m+1-p.val))%(2*m+1) := hv1
    refine Or.inr (Or.inr ⟨?_,?_,?_⟩)
    · rw [hu]; exact Nat.mod_lt _ (by omega)
    · rw [hv]; exact Nat.mod_lt _ (by omega)
    · rw [hu,hv,Nat.mod_add_mod,Nat.add_mod_mod]
      have he : c.val+p.val+(c.val+(2*m+1-p.val))=2*c.val+(2*m+1) := by omega
      rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]

private theorem color_symm {m} {c : Fin (2*m+1)} {u v : Fin (2*m+2)}
    (h : Color m c u v) : Color m c v u := by
  rcases h with h|h|⟨hu,hv,he⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨hv,hu,by simpa [Nat.add_comm] using he⟩)

private theorem color_unique {m} {c d : Fin (2*m+1)} {u v : Fin (2*m+2)}
    (hc : Color m c u v) (hd : Color m d u v) : c=d := by
  rcases hc with hc|hc|⟨hcu,hcv,hce⟩ <;>
    rcases hd with hd|hd|⟨hdu,hdv,hde⟩
  · exact Fin.ext (hc.2.symm.trans hd.2)
  · have hh := c.isLt; omega
  · omega
  · have hh := c.isLt; omega
  · exact Fin.ext (hc.2.symm.trans hd.2)
  · omega
  · omega
  · omega
  · exact double_inj m c d (hce.symm.trans hde)

private theorem vertex_zero (m : Nat) (c : Fin (2*m+1)) :
    (vertex m c (⟨0,by omega⟩,false)).val=c.val ∧
    (vertex m c (⟨0,by omega⟩,true)).val=2*m+1 := by
  have hc := c.isLt
  constructor <;> simp [vertex,rotate,base,Nat.mod_eq_of_lt hc]

private theorem edge_cover (m : Nat) (u v : Fin (2*m+2)) (hne : u≠v) :
    ∃ c : Fin (2*m+1), ∃ p : Fin (m+1),
      (vertex m c (p,false)=u ∧ vertex m c (p,true)=v) ∨
      (vertex m c (p,false)=v ∧ vertex m c (p,true)=u) := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases hui : u.val=2*m+1
  · have hvf : v.val<2*m+1 := by
      have hn : u.val≠v.val := fun h => hne (Fin.ext h)
      omega
    let c : Fin (2*m+1) := ⟨v.val,hvf⟩
    refine ⟨c,⟨0,by omega⟩,Or.inr ⟨Fin.ext (vertex_zero m c).1,Fin.ext ?_⟩⟩
    exact (vertex_zero m c).2.trans hui.symm
  by_cases hvi : v.val=2*m+1
  · have huf : u.val<2*m+1 := by omega
    let c : Fin (2*m+1) := ⟨u.val,huf⟩
    refine ⟨c,⟨0,by omega⟩,Or.inl ⟨Fin.ext (vertex_zero m c).1,Fin.ext ?_⟩⟩
    exact (vertex_zero m c).2.trans hvi.symm
  have huf : u.val<2*m+1 := by omega
  have hvf : v.val<2*m+1 := by omega
  let z : Fin (2*m+1) := ⟨(u.val+v.val)%(2*m+1),Nat.mod_lt _ (by omega)⟩
  obtain ⟨c,hc⟩ := double_surj m z
  obtain ⟨x,hx⟩ := rotate_surj m c u
  obtain ⟨y,hy⟩ := rotate_surj m c v
  have hxl := x.isLt
  have hyl := y.isLt
  have hcl := c.isLt
  have hvx := rotate_val m c x
  have hvy := rotate_val m c y
  rw [hx] at hvx
  rw [hy] at hvy
  have hxi : x.val≠2*m+1 := by intro hi; simp [hi] at hvx; omega
  have hyi : y.val≠2*m+1 := by intro hi; simp [hi] at hvy; omega
  simp only [hxi,hyi,ite_false] at hvx hvy
  have hxf : x.val<2*m+1 := by omega
  have hyf : y.val<2*m+1 := by omega
  have hxne : x.val≠y.val := by intro he; exact hne (hx.symm.trans ((congrArg (rotate m c) (Fin.ext he)).trans hy))
  have h1 := mod_cases (n:=2*m+1) (x:=c.val+x.val) (by omega) (by omega)
  have h2 := mod_cases (n:=2*m+1) (x:=c.val+y.val) (by omega) (by omega)
  have h3 := mod_cases (n:=2*m+1) (x:=u.val+v.val) (by omega) (by omega)
  have h4 := mod_cases (n:=2*m+1) (x:=2*c.val) (by omega) (by omega)
  change (2*c.val)%(2*m+1)=(u.val+v.val)%(2*m+1) at hc
  have hs : x.val+y.val=2*m+1 := by omega
  by_cases hp : x.val<m+1
  · let p : Fin (m+1) := ⟨x.val,hp⟩
    have hb0 : base m (p,false)=x := Fin.ext rfl
    have hb1 : base m (p,true)=y := Fin.ext (by change 2*m+1-x.val=y.val; omega)
    exact ⟨c,p,Or.inl ⟨by unfold vertex; rw [hb0,hx],by unfold vertex; rw [hb1,hy]⟩⟩
  · let p : Fin (m+1) := ⟨y.val,by omega⟩
    have hb0 : base m (p,false)=y := Fin.ext rfl
    have hb1 : base m (p,true)=x := Fin.ext (by change 2*m+1-y.val=x.val; omega)
    exact ⟨c,p,Or.inr ⟨by unfold vertex; rw [hb0,hy],by unfold vertex; rw [hb1,hx]⟩⟩


/-- Circle-method factorization of every even complete graph, constructed
uniformly; the last vertex is fixed while the odd cyclic part is rotated. -/
def factorization (m : Nat) : MatchingFactorization (Fin (2*m+2)) (fun u v => u≠v) (2*m+1) where
  Pair := Fin (m+1)
  pairs := List.ofFn id
  complete := fun p => List.mem_ofFn.mpr ⟨p,rfl⟩
  vertex := vertex m
  injective := fun c => fun _ _ h => base_inj m (rotate_inj m c h)
  surjective := by
    intro c u
    obtain ⟨x,hx⟩ := rotate_surj m c u
    obtain ⟨p,hp⟩ := base_surj m x
    exact ⟨p,by unfold vertex; rw [hp,hx]⟩
  edge_iff := by
    intro u v
    constructor
    · intro h
      obtain ⟨c,p,hp⟩ := edge_cover m u v h
      refine ⟨c,p,?_⟩
      rcases hp with ⟨h0,h1⟩|⟨h0,h1⟩
      · exact Or.inl (Prod.ext h0 h1)
      · exact Or.inr (Prod.ext h0 h1)
    · rintro ⟨c,p,hp⟩ he
      have hn : vertex m c (p,false)≠vertex m c (p,true) := by
        intro hh
        have hb := base_inj m (rotate_inj m c hh)
        have := congrArg Prod.snd hb
        contradiction
      rcases hp with hp|hp
      · exact hn ((congrArg Prod.fst hp).trans (he.trans (congrArg Prod.snd hp).symm))
      · exact hn ((congrArg Prod.fst hp).trans (he.symm.trans (congrArg Prod.snd hp).symm))
  color_unique := by
    intro c d p q he
    have hc := color_vertex m c p
    have hd := color_vertex m d q
    rcases he with he|he
    · have h0 := congrArg Prod.fst he
      have h1 := congrArg Prod.snd he
      simp only at h0 h1
      rw [←h0,←h1] at hd
      exact color_unique hc hd
    · have h0 := congrArg Prod.fst he
      have h1 := congrArg Prod.snd he
      simp only at h0 h1
      rw [←h1,←h0] at hd
      exact color_unique hc (color_symm hd)

end RoundRobin

/-- Standard q-letter Hamming adjacency. -/
def HammingAdjacent {t q : Nat} (u v : Fin t → Fin q) : Prop :=
  ∃ j, u j≠v j ∧ ∀ i, i≠j → u i=v i

/-- Uniform specialization to every positive even alphabet, without a
factorization premise. -/
theorem hamming_even_paths (t q L : Nat) (ht : 2≤t) (heven : t%2=0)
    (hq : 2≤q) (hqeven : q%2=0) (hL : 1≤L) (hlt : L<2^t)
    (hdiv : L∣t*2^(t-1)) : HasPaths (@HammingAdjacent t q) L := by
  let m := q/2-1
  have he : q=2*m+2 := by dsimp [m]; omega
  rw [he]
  exact paths (fun _ : Fin t => RoundRobin.factorization m) L ht heven hL hlt hdiv

#print axioms RoundRobin.factorization
#print axioms hamming_even_paths

namespace EvenCycle

/-- Standard cyclic adjacency on the numbered vertices of C_(2m). -/
def Adj (m : Nat) (u v : Fin (2*m)) : Prop :=
  (u.val+1)%(2*m)=v.val ∨ (v.val+1)%(2*m)=u.val

def vertex (m : Nat) (hm : 2≤m) (c : Fin 2) (p : Fin m × Bool) : Fin (2*m) :=
  ⟨(2*p.1.val+c.val+p.2.toNat)%(2*m),Nat.mod_lt _ (by omega)⟩

private theorem vertex_inj (m : Nat) (hm : 2≤m) (c : Fin 2) :
    Function.Injective (vertex m hm c) := by
  rintro ⟨p,b⟩ ⟨q,d⟩ h
  have hp := p.isLt
  have hq := q.isLt
  have hc := c.isLt
  have h1 := RoundRobin.mod_cases (n:=2*m) (x:=2*p.val+c.val+b.toNat) (by omega) (by cases b <;> simp <;> omega)
  have h2 := RoundRobin.mod_cases (n:=2*m) (x:=2*q.val+c.val+d.toNat) (by omega) (by cases d <;> simp <;> omega)
  have hv := congrArg Fin.val h
  change (2*p.val+c.val+b.toNat)%(2*m)=(2*q.val+c.val+d.toNat)%(2*m) at hv
  have hpq : p=q := Fin.ext (by cases b <;> cases d <;> simp at h1 h2 hv <;> omega)
  have hbd : b=d := by cases b <;> cases d <;> simp at h1 h2 hv ⊢ <;> omega
  exact Prod.ext hpq hbd

private theorem vertex_surj (m : Nat) (hm : 2≤m) (c : Fin 2) :
    Function.Surjective (vertex m hm c) := by
  intro x
  have hx := x.isLt
  have hc := c.isLt
  let z := if c.val≤x.val then x.val-c.val else x.val+2*m-c.val
  have hz : z<2*m := by dsimp [z]; split <;> omega
  let p : Fin m := ⟨z/2,by omega⟩
  let b : Bool := decide (z%2=1)
  have he : 2*p.val+b.toNat=z := by
    by_cases hh : z%2=1 <;> simp [p,b,hh] <;> omega
  refine ⟨(p,b),Fin.ext ?_⟩
  change (2*p.val+c.val+b.toNat)%(2*m)=x.val
  have hh : 2*p.val+c.val+b.toNat=z+c.val := by omega
  rw [hh]
  dsimp [z]
  split
  · have hh : x.val-c.val+c.val=x.val := by omega
    rw [hh,Nat.mod_eq_of_lt hx]
  · have hh : x.val+2*m-c.val+c.val=x.val+2*m := by omega
    rw [hh,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hx]

private theorem vertex_edge (m : Nat) (hm : 2≤m) (c : Fin 2) (p : Fin m) :
    ((vertex m hm c (p,false)).val+1)%(2*m)=(vertex m hm c (p,true)).val := by
  change (((2*p.val+c.val)%(2*m))+1)%(2*m)=(2*p.val+c.val+1)%(2*m)
  exact Nat.mod_add_mod _ _ _

private theorem oriented_unique (m : Nat) (hm : 2≤m) (u v : Fin (2*m))
    (h0 : (u.val+1)%(2*m)=v.val) (h1 : (v.val+1)%(2*m)=u.val) : False := by
  have hu := u.isLt
  have hv := v.isLt
  have h2 := RoundRobin.mod_cases (n:=2*m) (x:=u.val+1) (by omega) (by omega)
  have h3 := RoundRobin.mod_cases (n:=2*m) (x:=v.val+1) (by omega) (by omega)
  omega

def factorization (m : Nat) (hm : 2≤m) : MatchingFactorization (Fin (2*m)) (Adj m) 2 where
  Pair := Fin m
  pairs := List.ofFn id
  complete := fun p => List.mem_ofFn.mpr ⟨p,rfl⟩
  vertex := vertex m hm
  injective := vertex_inj m hm
  surjective := vertex_surj m hm
  edge_iff := by
    intro u v
    constructor
    · intro h
      have make (x y : Fin (2*m)) (he : (x.val+1)%(2*m)=y.val) :
          ∃ c p, SameEdge (vertex m hm c (p,false),vertex m hm c (p,true)) (x,y) := by
        let c : Fin 2 := ⟨x.val%2,Nat.mod_lt _ (by decide)⟩
        let p : Fin m := ⟨x.val/2,by have := x.isLt; omega⟩
        have hx : vertex m hm c (p,false)=x := by
          apply Fin.ext
          change (2*(x.val/2)+x.val%2)%(2*m)=x.val
          rw [Nat.div_add_mod,Nat.mod_eq_of_lt x.isLt]
        have hy : vertex m hm c (p,true)=y := by
          apply Fin.ext
          rw [←vertex_edge m hm c p,hx,he]
        exact ⟨c,p,Or.inl (Prod.ext hx hy)⟩
      rcases h with h|h
      · exact make u v h
      · obtain ⟨c,p,hp⟩ := make v u h
        refine ⟨c,p,?_⟩
        rcases hp with hp|hp
        · exact Or.inr hp
        · exact Or.inl hp
    · rintro ⟨c,p,he⟩
      have h := vertex_edge m hm c p
      rcases he with he|he
      · have h0 := congrArg Prod.fst he
        have h1 := congrArg Prod.snd he
        simp only at h0 h1
        rw [h0,h1] at h
        exact Or.inl h
      · have h0 := congrArg Prod.fst he
        have h1 := congrArg Prod.snd he
        simp only at h0 h1
        rw [h0,h1] at h
        exact Or.inr h
  color_unique := by
    intro c d p q he
    have hp := p.isLt
    have hq := q.isLt
    have hc := c.isLt
    have hd := d.isLt
    rcases he with he|he
    · have hh := congrArg (fun z => z.1.val) he
      change (2*p.val+c.val)%(2*m)=(2*q.val+d.val)%(2*m) at hh
      rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hh
      exact Fin.ext (by omega)
    · have h0 := vertex_edge m hm c p
      have h1 := vertex_edge m hm d q
      have ha := congrArg Prod.fst he
      have hb := congrArg Prod.snd he
      simp only at ha hb
      rw [←hb,←ha] at h1
      exact False.elim (oriented_unique m hm _ _ h0 h1)

end EvenCycle

/-- Products of arbitrary even cycles C_(2m_i), each of length at least four. -/
theorem even_torus_paths {t : Nat} (m : Fin t → Nat) (hm : ∀ i, 2≤m i)
    (L : Nat) (ht : 2≤t) (heven : t%2=0) (hL : 1≤L) (hlt : L<2^t)
    (hdiv : L∣t*2^(t-1)) :
    HasPaths (CartesianAdjacent (fun i => EvenCycle.Adj (m i))) L :=
  paths (fun i => EvenCycle.factorization (m i) (hm i)) L ht heven hL hlt hdiv

#print axioms EvenCycle.factorization
#print axioms even_torus_paths

/-- Path cases of the regular-bipartite tree-decomposition conjecture:
path length equals the product's degree. -/
theorem regular_bipartite_degree_paths {t : Nat} {N : Fin t → Nat}
    (G : ∀ i, HallColor.Bipartite (N i) (N i)) (s : Nat)
    (hSimple : ∀ i, Bipartite.Simple (G i)) (hRegular : ∀ i, (G i).Regular (2^s))
    (ht : 2≤t) (heven : t%2=0) (hlt : t*2^s<2^t) :
    HasPaths (CartesianAdjacent (fun i => Bipartite.Adj (G i))) (t*2^s) := by
  have hp := Nat.two_pow_pos s
  have h1 : 2^(s+1)≤t*2^s := by
    rw [Nat.pow_succ,Nat.mul_comm (2^s) 2]
    exact Nat.mul_le_mul_right _ ht
  have h2 : s+1<t := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
    (Nat.lt_of_le_of_lt h1 hlt)
  exact regular_bipartite_paths G hSimple hRegular _ ht heven
    (by exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) hp)) hlt
    (Nat.mul_dvd_mul_left t (Nat.pow_dvd_pow 2 (by omega)))

/-- A path case of the 2m-regular tree-decomposition conjecture as well. -/
theorem regular_bipartite_six_sixteen {N : Fin 6 → Nat}
    (G : ∀ i, HallColor.Bipartite (N i) (N i))
    (hSimple : ∀ i, Bipartite.Simple (G i)) (hRegular : ∀ i, (G i).Regular 16) :
    HasPaths (CartesianAdjacent (fun i => Bipartite.Adj (G i))) 48 :=
  regular_bipartite_paths G hSimple hRegular 48
    (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms regular_bipartite_degree_paths
#print axioms regular_bipartite_six_sixteen

end ErdePaths.Consequences.ProductTransfer
