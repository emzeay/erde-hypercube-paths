import ErdePaths.AnchoredEmbedding

namespace ErdePaths.AnchoredAssembly
open SquareLift AnchoredEmbedding SubdividedWiggle

/-- Explicit cyclic factors and spaced representatives. No host partition or
path existence is among these input fields. -/
structure FactorData (V W : Type) (R : V → V → Prop) (S : W → W → Prop)
    (a B s m q : Nat) (ha : 0<a) (hB : 0<B) (hs : 0<s) where
  G : Fin m → Fin ((2*a)*s) → V
  H : Fin q → Fin B → W
  association : Fin m → Fin q
  G_injective : ∀ i, Function.Injective (G i)
  H_injective : ∀ j, Function.Injective (H j)
  G_surjective : ∀ i, Function.Surjective (G i)
  H_surjective : ∀ j, Function.Surjective (H j)
  R_symm : ∀ u v, R u v → R v u
  S_symm : ∀ u v, S u v → S v u
  R_loopfree : ∀ u, ¬R u u
  S_loopfree : ∀ u, ¬S u u
  G_adjacent : ∀ i t, R (G i t)
    (G i (successor (Nat.mul_pos (show 0<2*a by omega) hs) t))
  H_adjacent : ∀ j t, S (H j t) (H j (successor hB t))
  G_cover : ∀ u v, R u v → ∃ i t, SameEdge
    (G i t,G i (successor (Nat.mul_pos (show 0<2*a by omega) hs) t)) (u,v)
  H_cover : ∀ u v, S u v → ∃ j t, SameEdge (H j t,H j (successor hB t)) (u,v)
  G_unique : ∀ i t k z, SameEdge
    (G i t,G i (successor (Nat.mul_pos (show 0<2*a by omega) hs) t))
    (G k z,G k (successor (Nat.mul_pos (show 0<2*a by omega) hs) z)) → i=k ∧ t=z
  H_unique : ∀ j t k z, SameEdge (H j t,H j (successor hB t))
    (H k z,H k (successor hB z)) → j=k ∧ t=z
  representative_cover : ∀ j u, ∃ i k, association i=j ∧ G i (positionEncode k ⟨0,hs⟩)=u
  representative_unique : ∀ i k i' k', association i=association i' →
    G i (positionEncode k ⟨0,hs⟩)=G i' (positionEncode k' ⟨0,hs⟩) → i=i' ∧ k=k'

variable {V W : Type} {R : V → V → Prop} {S : W → W → Prop}
variable {a B s m q : Nat} {ha : 0<a} {hB : 0<B} {hs : 0<s}

abbrev Host (d : FactorData V W R S a B s m q ha hB hs) (i : Fin m) :=
  AnchoredHost ha hB hs (d.G i) (d.H (d.association i))

private theorem sameEdge_const_right {x y : V} {z : W} {u v : V × W}
    (h : SameEdge ((x,z),(y,z)) (u,v)) : u.2=v.2 := by
  rcases h with h | h
  · have h1 := congrArg (fun e : (V×W)×(V×W) => e.1.2) h
    have h2 := congrArg (fun e : (V×W)×(V×W) => e.2.2) h
    exact h1.symm.trans h2
  · have h1 := congrArg (fun e : (V×W)×(V×W) => e.1.2) h
    have h2 := congrArg (fun e : (V×W)×(V×W) => e.2.2) h
    exact h2.symm.trans h1

private theorem sameEdge_const_left {x : V} {z w : W} {u v : V × W}
    (h : SameEdge ((x,z),(x,w)) (u,v)) : u.1=v.1 ∧ x=u.1 := by
  rcases h with h | h
  · have h1 := congrArg (fun e : (V×W)×(V×W) => e.1.1) h
    have h2 := congrArg (fun e : (V×W)×(V×W) => e.2.1) h
    exact ⟨h1.symm.trans h2,h1⟩
  · have h1 := congrArg (fun e : (V×W)×(V×W) => e.1.1) h
    have h2 := congrArg (fun e : (V×W)×(V×W) => e.2.1) h
    exact ⟨h2.symm.trans h1,h2⟩

/-- Projection of actual host generators preserves their actual edge labels. -/
theorem host_classify (d : FactorData V W R S a B s m q ha hB hs)
    {i : Fin m} {u v : V×W} (h : Host d i u v) :
    (u.2=v.2 ∧ ∃ t, SameEdge
      (d.G i t,d.G i (successor (Nat.mul_pos (show 0<2*a by omega) hs) t)) (u.1,v.1)) ∨
    (u.1=v.1 ∧ ∃ k, d.G i (positionEncode k ⟨0,hs⟩)=u.1 ∧
      ∃ t, SameEdge (d.H (d.association i) t,d.H (d.association i) (successor hB t)) (u.2,v.2)) := by
  rcases h with ⟨t,j,he⟩ | ⟨k,t,he⟩
  · exact Or.inl ⟨sameEdge_const_right he,t,map_sameEdge Prod.fst he⟩
  · obtain ⟨hu,hanchor⟩ := sameEdge_const_left he
    exact Or.inr ⟨hu,k,hanchor,t,map_sameEdge Prod.snd he⟩

private theorem relation_of_sameEdge {X : Type} {T : X → X → Prop}
    (hT : ∀ x y, T x y → T y x) {x y u v : X}
    (hxy : T x y) (he : SameEdge (x,y) (u,v)) : T u v := by
  rcases he with he | he
  · have hu : x=u := congrArg Prod.fst he
    have hv : y=v := congrArg Prod.snd he
    simpa only [hu,hv] using hxy
  · have hv : x=v := congrArg Prod.fst he
    have hu : y=u := congrArg Prod.snd he
    simpa only [hu,hv] using hT x y hxy

/-- Every true Cartesian-product edge has an explicitly decoded host owner. -/
theorem host_cover (d : FactorData V W R S a B s m q ha hB hs)
    {u v : V×W} (h : ProductRelation R S u v) : ∃ i, Host d i u v := by
  rcases h with ⟨hw,hr⟩ | ⟨hv,hr⟩
  · obtain ⟨i,t,he⟩ := d.G_cover u.1 v.1 hr
    obtain ⟨j,hj⟩ := d.H_surjective (d.association i) u.2
    refine ⟨i,Or.inl ⟨t,j,?_⟩⟩
    have hem := map_sameEdge (fun x : V => (x,u.2)) he
    have hU : (u.1,v.2)=u := Prod.ext rfl hw.symm
    simpa only [hj,hw,Prod.eta,hU] using hem
  · obtain ⟨j,t,he⟩ := d.H_cover u.2 v.2 hr
    obtain ⟨i,k,hassoc,hanchor⟩ := d.representative_cover j u.1
    refine ⟨i,Or.inr ⟨k,t,?_⟩⟩
    rw [hassoc]
    have hem := map_sameEdge (fun y : W => (u.1,y)) he
    have hU : (v.1,u.2)=u := Prod.ext hv.symm rfl
    simpa only [hanchor,hv,Prod.eta,hU] using hem

/-- Two different hosts cannot own one actual undirected product edge. -/
theorem host_unique (d : FactorData V W R S a B s m q ha hB hs)
    {i k : Fin m} {u v : V×W} (hi : Host d i u v) (hk : Host d k u v) : i=k := by
  rcases host_classify d hi with ⟨hW,t,ht⟩ | ⟨hV,c,hc,t,ht⟩
  · rcases host_classify d hk with ⟨_,z,hz⟩ | ⟨hV,_,_,_,_⟩
    · exact (d.G_unique i t k z (sameEdge_trans ht (sameEdge_symm hz))).1
    · have hr := relation_of_sameEdge d.R_symm (d.G_adjacent i t) ht
      rw [hV] at hr
      exact False.elim (d.R_loopfree _ hr)
  · rcases host_classify d hk with ⟨_,z,hz⟩ | ⟨_,c',hc',z,hz⟩
    · have hr := relation_of_sameEdge d.R_symm (d.G_adjacent k z) hz
      rw [hV] at hr
      exact False.elim (d.R_loopfree _ hr)
    · have hj := (d.H_unique (d.association i) t (d.association k) z
        (sameEdge_trans ht (sameEdge_symm hz))).1
      exact (d.representative_unique i c k c' hj (hc.trans hc'.symm)).1

theorem host_subset (d : FactorData V W R S a B s m q ha hB hs)
    {i : Fin m} {u v : V×W} (h : Host d i u v) : ProductRelation R S u v :=
  host_in_product ha hB hs (d.G i) (d.H (d.association i)) R S
    d.R_symm d.S_symm (d.G_adjacent i) (d.H_adjacent (d.association i)) h

/-- Exact global host union on the ordinary Cartesian-product edge relation. -/
theorem host_union_exact (d : FactorData V W R S a B s m q ha hB hs) (u v : V×W) :
    ProductRelation R S u v ↔ ∃ i, Host d i u v :=
  ⟨host_cover d,fun ⟨_,h⟩ => host_subset d h⟩

/-- Explicit finite host/path index list. -/
def assemblyIndices (m : Nat) : List (Fin m × Bool) :=
  (List.ofFn (fun i : Fin m => i)).flatMap (fun i => [(i,false),(i,true)])

theorem mem_assemblyIndices (p : Fin m × Bool) : p ∈ assemblyIndices m := by
  rcases p with ⟨i,b⟩
  cases b <;> simp [assemblyIndices,List.mem_flatMap,List.mem_ofFn]

def localPaths (d : FactorData V W R S a B s m q ha hB hs)
    (ha2 : 2≤a) (hB4 : 4≤B) (heven : B%2=0) (hs2 : 2≤s) (i : Fin m) :=
  anchoredPathDecomposition ha2 hB4 heven hs2 (d.G i) (d.H (d.association i))
    (d.G_injective i) (d.H_injective (d.association i))

private theorem mem_localPaths (d : FactorData V W R S a B s m q ha hB hs)
    (ha2 : 2≤a) (hB4 : 4≤B) (heven : B%2=0) (hs2 : 2≤s) (i : Fin m) (b : Bool) :
    b ∈ (localPaths d ha2 hB4 heven hs2 i).indices := by
  change b ∈ [false,true]
  cases b <;> decide

/-- Assembly of explicit local paths. Global uniqueness is proved from factor
and representative ownership, not from a host-partition assumption. -/
def productPathDecomposition (d : FactorData V W R S a B s m q ha hB hs)
    (ha2 : 2≤a) (hB4 : 4≤B) (heven : B%2=0) (hs2 : 2≤s) :
    GraphPathDecomposition (V×W) (ProductRelation R S) (ForkWiggle.cycleLength a B s) where
  Index := Fin m × Bool
  indices := assemblyIndices m
  vertices := fun p => (localPaths d ha2 hB4 heven hs2 p.1).vertices p.2
  simple := by
    intro p _
    exact (localPaths d ha2 hB4 heven hs2 p.1).simple p.2
      (mem_localPaths d ha2 hB4 heven hs2 p.1 p.2)
  adjacent := by
    intro p _ j
    exact host_subset d ((localPaths d ha2 hB4 heven hs2 p.1).adjacent p.2
      (mem_localPaths d ha2 hB4 heven hs2 p.1 p.2) j)
  cover := by
    intro u v huv
    obtain ⟨i,hi⟩ := host_cover d huv
    obtain ⟨b,hb,j,he⟩ := (localPaths d ha2 hB4 heven hs2 i).cover u v hi
    exact ⟨(i,b),mem_assemblyIndices (i,b),j,he⟩
  unique := by
    intro p q _ _ j k he
    rcases p with ⟨i,b⟩
    rcases q with ⟨i',b'⟩
    have hbi := mem_localPaths d ha2 hB4 heven hs2 i b
    have hb'i := mem_localPaths d ha2 hB4 heven hs2 i' b'
    have hi := (localPaths d ha2 hB4 heven hs2 i).adjacent b hbi j
    have hi' := (localPaths d ha2 hB4 heven hs2 i').adjacent b' hb'i k
    have htarget : Host d i
        ((localPaths d ha2 hB4 heven hs2 i').vertices b' k.castSucc)
        ((localPaths d ha2 hB4 heven hs2 i').vertices b' k.succ) :=
      host_sameEdge ha hB hs (d.G i) (d.H (d.association i)) hi he
    have hii' := host_unique d htarget hi'
    subst i'
    obtain ⟨hbb',hjk⟩ := (localPaths d ha2 hB4 heven hs2 i).unique b b' hbi hb'i j k he
    exact ⟨Prod.ext rfl hbb',hjk⟩

/-- Genuine Cartesian-product path decomposition at the exact balanced length. -/
def productPathDecompositionExact (d : FactorData V W R S a B s m q ha hB hs)
    (ha2 : 2≤a) (hB4 : 4≤B) (heven : B%2=0) (hs2 : 2≤s) :
    GraphPathDecomposition (V×W) (ProductRelation R S) ((2*a)*B*(s+1)/2) := by
  rw [←ForkWiggle.finePath_length a B s]
  exact productPathDecomposition d ha2 hB4 heven hs2

#print axioms productPathDecompositionExact
#print axioms host_cover
#print axioms host_unique
#print axioms host_subset
end ErdePaths.AnchoredAssembly
