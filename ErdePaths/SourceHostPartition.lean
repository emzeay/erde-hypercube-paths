import ErdePaths.SourceOrientedFactors
import ErdePaths.SourceAnchorCoordinates
import ErdePaths.AnchoredAssembly

namespace ErdePaths.SourceHostPartition
open SourceClock SourceProfile HamiltonData HamiltonTower HierarchicalDecode SquareLift
open AnchoredEmbedding SourceAnchorGroups SubdividedWiggle

/-- Literal group key, including the initial Hamilton factor. -/
abbrev Key (m K r : Nat) := Fin m × Bool × Vertex (K-r)

def boolIndex (b : Bool) : Fin 2 := if b then ⟨1,by decide⟩ else ⟨0,by decide⟩
def indexBool (b : Fin 2) : Bool := b.val=1

theorem indexBool_boolIndex (b : Bool) : indexBool (boolIndex b)=b := by cases b <;> decide

theorem boolIndex_indexBool (b : Fin 2) : boolIndex (indexBool b)=b := by
  apply Fin.ext
  have := b.isLt
  simp only [boolIndex,indexBool]
  by_cases hb : b.val=1
  · simp [hb]
  · simp [hb]; omega

/-- A canonical assignment to all H factor indices, not an ownership premise. -/
def keyIndex {m K r : Nat} (k : Key m K r) : Fin (m*(2*2^(K-r))) :=
  positionEncode k.1 (positionEncode (boolIndex k.2.1) k.2.2)

def indexKey {m K r : Nat} (q : Fin (m*(2*2^(K-r)))) : Key m K r :=
  let p := positionDecode (Nat.mul_pos (by decide : 0<2) (Nat.two_pow_pos (K-r))) q
  let t := positionDecode (Nat.two_pow_pos (K-r)) p.2
  (p.1,indexBool t.1,t.2)

theorem indexKey_keyIndex {m K r : Nat} (k : Key m K r) : indexKey (keyIndex k)=k := by
  simp only [indexKey,keyIndex,positionDecode_encode,indexBool_boolIndex,Prod.eta]

theorem keyIndex_indexKey {m K r : Nat} (q : Fin (m*(2*2^(K-r)))) : keyIndex (indexKey q)=q := by
  simp only [indexKey,keyIndex,boolIndex_indexBool,positionEncode_decode]

theorem keyIndex_injective {m K r : Nat} : Function.Injective (@keyIndex m K r) := by
  intro x y he
  simpa only [indexKey_keyIndex] using congrArg indexKey he

noncomputable def highKey {K : Nat} (r : Nat) (hr : r≤K) (address : Address K) : Vertex (K-r) :=
  Classical.choose (highAddress_covers r hr address)

theorem highKey_group {K : Nat} (r : Nat) (hr : r≤K) (address : Address K) :
    InGroup r (highAddress r hr (highKey r hr address)) address :=
  Classical.choose_spec (highAddress_covers r hr address)

theorem highKey_eq {K : Nat} (r : Nat) (hr : r≤K) (high : Vertex (K-r))
    (address : Address K) (hg : InGroup r (highAddress r hr high) address) :
    highKey r hr address=high :=
  highAddress_unique r hr _ _ address (highKey_group r hr address) hg

/-- An actual undirected edge of one displayed Hamilton factor. -/
def FactorEdge {X : Type} {T : X→X→Prop} {M N : Nat} {hN : 0<N}
    (F : DecompositionData X T M N hN) (i : Fin M) (x y : X) : Prop :=
  ∃t, SameEdge ((F.cycles i).cycle t,(F.cycles i).cycle (successor hN t)) (x,y)

theorem factorEdge_relation {X : Type} {T : X→X→Prop} {M N : Nat} {hN : 0<N}
    (F : DecompositionData X T M N hN) {i x y} (he : FactorEdge F i x y) : T x y := by
  obtain ⟨t,ht⟩ := he
  have ha := (F.cycles i).adjacent t
  rcases ht with ht | ht
  · have hx := congrArg Prod.fst ht
    have hy := congrArg Prod.snd ht
    change (F.cycles i).cycle t=x at hx
    change (F.cycles i).cycle (successor hN t)=y at hy
    rw [hx,hy] at ha
    exact ha
  · have hy := congrArg Prod.fst ht
    have hx := congrArg Prod.snd ht
    change (F.cycles i).cycle t=y at hy
    change (F.cycles i).cycle (successor hN t)=x at hx
    have hb := F.symmetric _ _ ha
    rw [hx,hy] at hb
    exact hb

theorem factorEdge_unique {X : Type} {T : X→X→Prop} {M N : Nat} {hN : 0<N}
    (F : DecompositionData X T M N hN) {i k x y}
    (hi : FactorEdge F i x y) (hk : FactorEdge F k x y) : i=k := by
  obtain ⟨t,ht⟩ := hi
  obtain ⟨z,hz⟩ := hk
  exact (F.unique i t k z (sameEdge_trans ht
    (sameEdge_symm hz))).1

private theorem constant_right {X Y : Type} {a b : X} {w : Y} {x y : X×Y}
    (he : SameEdge ((a,w),(b,w)) (x,y)) : x.2=y.2 := by
  rcases he with he | he
  · have hx := congrArg (fun p : (X×Y)×(X×Y)=>p.1.2) he
    have hy := congrArg (fun p : (X×Y)×(X×Y)=>p.2.2) he
    exact hx.symm.trans hy
  · have hy := congrArg (fun p : (X×Y)×(X×Y)=>p.1.2) he
    have hx := congrArg (fun p : (X×Y)×(X×Y)=>p.2.2) he
    exact hx.symm.trans hy

private theorem constant_left {X Y : Type} {w : X} {a b : Y} {x y : X×Y}
    (he : SameEdge ((w,a),(w,b)) (x,y)) : x.1=y.1 ∧ w=x.1 := by
  rcases he with he | he
  · have hx := congrArg (fun p : (X×Y)×(X×Y)=>p.1.1) he
    have hy := congrArg (fun p : (X×Y)×(X×Y)=>p.2.1) he
    exact ⟨hx.symm.trans hy,hx⟩
  · have hy := congrArg (fun p : (X×Y)×(X×Y)=>p.1.1) he
    have hx := congrArg (fun p : (X×Y)×(X×Y)=>p.2.1) he
    exact ⟨hx.symm.trans hy,hx⟩

section Source
variable {V : Type} {R : V→V→Prop} {m e u : Nat}
  (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)
  (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
  (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
  (S : Fin m→Address a→Fin (2^(e*2^a))→Bool)
  (ho : ∀f address, Profile.cardinality (S f address)%2=1)
  (hb : ∀f, ∀address : Address (a+h), Profile.prefixCount (S f (lowerAddress address)) (2*u)=u)


/-- Actual initial-factor/twin/high-address decoding of every owned G factor. -/
noncomputable def groupKey (q : Fin (count (2*count m a) h)) : Key m (a+h) r :=
  let cfg := SourceOrientedFactors.configuration a h q
  (cfg.1,cfg.2.1,highKey r (Nat.le_of_lt_succ hr) cfg.2.2)

noncomputable def association (q : Fin (count (2*count m a) h)) : Fin (m*(2*2^(a+h-r))) := keyIndex (groupKey a h r hr q)

theorem association_index (f : Fin m) (epsilon : Bool) (address : Address (a+h)) :
    association a h r hr (SourceFactors.index a h f epsilon address)=
      keyIndex (f,epsilon,highKey r (Nat.le_of_lt_succ hr) address) := by
  simp only [association,groupKey,SourceOrientedFactors.index_configuration]

/-- Every assigned H factor and every physical G vertex has one actual G
old-grid representative; all ownership is derived from source decoding. -/
theorem representative_cover (z : Fin (2^r)) (j : Fin (m*(2*2^(a+h-r)))) (v : (VertexPower (VertexPower V a×VertexPower V a) h)) :
    ∃i : Fin (count (2*count m a) h), association a h r hr i=j ∧
      (((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).position v).val%(2^r)=0 := by
  let key := indexKey j
  obtain ⟨address,hgroup,hgrid,_⟩ := SourceAnchorCoordinates.unique_grid_owner he
    (D.cycles key.1).toClockData a h r hr hh room hA (S key.1) (ho key.1) (hb key.1)
    key.2.1 (highAddress r (Nat.le_of_lt_succ hr) key.2.2) z v
  refine ⟨SourceFactors.index a h key.1 key.2.1 address,?_,?_⟩
  · rw [association_index,highKey_eq r (Nat.le_of_lt_succ hr) key.2.2 address hgroup]
    exact keyIndex_indexKey j
  · rw [←SourceOrientedFactors.clock_eq D he a h r hr hh room hA S ho hb z] at hgrid
    exact hgrid

/-- Within one assigned H factor, actual old-grid representative ownership
is unique, including the initial Hamilton factor and the twin bit. -/
theorem representative_unique (z : Fin (2^r)) (i i' : Fin (count (2*count m a) h)) (v : (VertexPower (VertexPower V a×VertexPower V a) h))
    (heq : association a h r hr i=association a h r hr i')
    (hi : (((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).position v).val%(2^r)=0)
    (hi' : (((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i').position v).val%(2^r)=0) : i=i' := by
  let cfg := SourceOrientedFactors.configuration a h i
  let cfg' := SourceOrientedFactors.configuration a h i'
  have hk := keyIndex_injective heq
  have hf : cfg.1=cfg'.1 := congrArg (fun k : Key m (a+h) r=>k.1) hk
  have heps : cfg.2.1=cfg'.2.1 := congrArg (fun k : Key m (a+h) r=>k.2.1) hk
  have hhkey : highKey r (Nat.le_of_lt_succ hr) cfg.2.2=highKey r (Nat.le_of_lt_succ hr) cfg'.2.2 :=
    congrArg (fun k : Key m (a+h) r=>k.2.2) hk
  have hci := SourceOrientedFactors.configuration_index a h i
  have hci' := SourceOrientedFactors.configuration_index a h i'
  change SourceFactors.index a h cfg.1 cfg.2.1 cfg.2.2=i at hci
  change SourceFactors.index a h cfg'.1 cfg'.2.1 cfg'.2.2=i' at hci'
  rw [←hci,SourceOrientedFactors.clock_eq D he a h r hr hh room hA S ho hb z] at hi
  rw [←hci',SourceOrientedFactors.clock_eq D he a h r hr hh room hA S ho hb z,←hf,←heps] at hi'
  obtain ⟨owner,_,_,hu⟩ := SourceAnchorCoordinates.unique_grid_owner he
    (D.cycles cfg.1).toClockData a h r hr hh room hA (S cfg.1) (ho cfg.1) (hb cfg.1)
    cfg.2.1 (highAddress r (Nat.le_of_lt_succ hr) (highKey r (Nat.le_of_lt_succ hr) cfg.2.2)) z v
  have hgroup := highKey_group r (Nat.le_of_lt_succ hr) cfg.2.2
  have hgroup' := highKey_group r (Nat.le_of_lt_succ hr) cfg'.2.2
  rw [←hhkey] at hgroup'
  have had := (hu cfg.2.2 hgroup hi).trans (hu cfg'.2.2 hgroup' hi').symm
  exact hci.symm.trans ((congrArg (fun address=>SourceFactors.index a h cfg.1 cfg.2.1 address) had).trans
    (by rw [hf,heps]; exact hci'))

/-- Actual spaced representatives, with literal coarse indices rather than
just their derived inverse-clock predicate. -/
theorem representative_vertices_cover (z : Fin (2^r))
    (j : Fin (m*(2*2^(a+h-r)))) (v : VertexPower (VertexPower V a×VertexPower V a) h) :
    ∃i : Fin (count (2*count m a) h), ∃k : Fin (2^(e*2^(a+h+1)-r)),
      association a h r hr i=j ∧
      ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).cycle
        (positionEncode k ⟨0,Nat.two_pow_pos r⟩)=v := by
  obtain ⟨i,hai,hgrid⟩ := representative_cover D he a h r hr hh room hA S ho hb z j v
  obtain ⟨k,hk⟩ := (SourceAnchorCoordinates.anchor_vertices_iff (Nat.two_pow_pos r)
    ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).toClockData v).mpr hgrid
  exact ⟨i,k,hai,hk⟩

/-- Both the actual factor and the literal coarse occurrence index are unique
inside any canonically assigned H group. -/
theorem representative_vertices_unique (z : Fin (2^r))
    (i i' : Fin (count (2*count m a) h)) (k k' : Fin (2^(e*2^(a+h+1)-r)))
    (hai : association a h r hr i=association a h r hr i')
    (hv : ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).cycle
        (positionEncode k ⟨0,Nat.two_pow_pos r⟩)=
      ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i').cycle
        (positionEncode k' ⟨0,Nat.two_pow_pos r⟩)) : i=i' ∧ k=k' := by
  let v := ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).cycle
    (positionEncode k ⟨0,Nat.two_pow_pos r⟩)
  have hgi := (SourceAnchorCoordinates.anchor_vertices_iff (Nat.two_pow_pos r)
    ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).toClockData v).mp ⟨k,rfl⟩
  have hgi' := (SourceAnchorCoordinates.anchor_vertices_iff (Nat.two_pow_pos r)
    ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i').toClockData v).mp ⟨k',hv.symm⟩
  have hii := representative_unique D he a h r hr hh room hA S ho hb z i i' v hai hgi hgi'
  refine ⟨hii,?_⟩
  subst i'
  have hp := cycle_injective _ hv
  have hh := congrArg (positionDecode (Nat.two_pow_pos r)) hp
  exact congrArg Prod.fst (by simpa only [positionDecode_encode] using hh)

section Host
variable {W : Type} {T : W→W→Prop} {B : Nat} {hB : 0<B}
  (H : DecompositionData W T (m*(2*2^(a+h-r))) B hB)

/-- Literal anchored host classifier: every G edge at every H vertex, and
assigned H edges exactly at this actual G factor's coordinate-zero grid. -/
noncomputable def Host (z : Fin (2^r)) (i : Fin (count (2*count m a) h)) (x y : (VertexPower (VertexPower V a×VertexPower V a) h)×W) : Prop :=
  (x.2=y.2 ∧ FactorEdge (SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z) i x.1 y.1) ∨
  (x.1=y.1 ∧
    (((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).position x.1).val%(2^r)=0 ∧
    FactorEdge H (association a h r hr i) x.2 y.2)

/-- The proved host is exactly the literal actual anchored generators,
including every horizontal copy and only coordinate-zero vertical copies. -/
theorem host_generators_iff (z : Fin (2^r)) (i : Fin (count (2*count m a) h))
    (x y : (VertexPower (VertexPower V a×VertexPower V a) h)×W) :
    Host D he a h r hr hh room hA S ho hb H z i x y ↔
    (∃t : Fin (2^(e*2^(a+h+1)-r)*2^r), ∃j : Fin B,
      SameEdge
        ((((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).cycle t,
          (H.cycles (association a h r hr i)).cycle j),
         (((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).cycle
            (successor (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) t),
          (H.cycles (association a h r hr i)).cycle j)) (x,y)) ∨
    (∃k : Fin (2^(e*2^(a+h+1)-r)), ∃j : Fin B,
      SameEdge
        ((((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).cycle
            (positionEncode k ⟨0,Nat.two_pow_pos r⟩),
          (H.cycles (association a h r hr i)).cycle j),
         (((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i).cycle
            (positionEncode k ⟨0,Nat.two_pow_pos r⟩),
          (H.cycles (association a h r hr i)).cycle (successor hB j))) (x,y)) := by
  let G := (SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cycles i
  let J := H.cycles (association a h r hr i)
  change ((x.2=y.2 ∧ ∃t,SameEdge (G.cycle t,G.cycle (successor _ t)) (x.1,y.1)) ∨
      (x.1=y.1 ∧ (G.position x.1).val%(2^r)=0 ∧
        ∃j,SameEdge (J.cycle j,J.cycle (successor hB j)) (x.2,y.2))) ↔ _
  constructor
  · rintro (⟨hw,t,ht⟩ | ⟨hv,hgrid,j,hj⟩)
    · refine Or.inl ⟨t,J.position x.2,?_⟩
      have hem := map_sameEdge (fun v=>(v,x.2)) ht
      change SameEdge ((G.cycle t,J.cycle (J.position x.2)),
        (G.cycle (successor _ t),J.cycle (J.position x.2))) (x,y)
      rw [J.cycle_position]
      have hx : (x.1,y.2)=x := Prod.ext rfl hw.symm
      simpa only [hw,Prod.eta,hx] using hem
    · obtain ⟨k,hk⟩ := (SourceAnchorCoordinates.anchor_vertices_iff (Nat.two_pow_pos r) G.toClockData x.1).mpr hgrid
      refine Or.inr ⟨k,j,?_⟩
      have hem := map_sameEdge (fun w=>(x.1,w)) hj
      change SameEdge ((G.cycle (positionEncode k ⟨0,Nat.two_pow_pos r⟩),J.cycle j),
        (G.cycle (positionEncode k ⟨0,Nat.two_pow_pos r⟩),J.cycle (successor hB j))) (x,y)
      rw [hk]
      have hx : (y.1,x.2)=x := Prod.ext hv.symm rfl
      simpa only [hv,Prod.eta,hx] using hem
  · rintro (⟨t,j,ht⟩ | ⟨k,j,hj⟩)
    · exact Or.inl ⟨constant_right ht,t,map_sameEdge Prod.fst ht⟩
    · obtain ⟨hv,hanchor⟩ := constant_left hj
      refine Or.inr ⟨hv,?_,j,map_sameEdge Prod.snd hj⟩
      exact (SourceAnchorCoordinates.anchor_vertices_iff (Nat.two_pow_pos r) G.toClockData x.1).mp ⟨k,hanchor⟩

theorem host_subset (z : Fin (2^r)) {i : Fin (count (2*count m a) h)} {x y : (VertexPower (VertexPower V a×VertexPower V a) h)×W}
    (hi : Host D he a h r hr hh room hA S ho hb H z i x y) :
    ProductRelation (relation (ProductAdjacent (relation R a)) h) T x y := by
  rcases hi with ⟨hw,he⟩ | ⟨hv,_,he⟩
  · exact Or.inl ⟨hw,factorEdge_relation _ he⟩
  · exact Or.inr ⟨hv,factorEdge_relation H he⟩

/-- Full actual Cartesian edge coverage from the constructed factor data and
restricted source decoder; no host-cover or representative-cover premise. -/
theorem host_cover (z : Fin (2^r)) {x y : (VertexPower (VertexPower V a×VertexPower V a) h)×W}
    (hedge : ProductRelation (relation (ProductAdjacent (relation R a)) h) T x y) :
    ∃i : Fin (count (2*count m a) h), Host D he a h r hr hh room hA S ho hb H z i x y := by
  rcases hedge with ⟨hw,hedge⟩ | ⟨hv,hedge⟩
  · obtain ⟨i,t,ht⟩ := (SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).cover x.1 y.1 hedge
    exact ⟨i,Or.inl ⟨hw,t,ht⟩⟩
  · obtain ⟨j,t,ht⟩ := H.cover x.2 y.2 hedge
    obtain ⟨i,hai,hgrid⟩ := representative_cover D he a h r hr hh room hA S ho hb z j x.1
    exact ⟨i,Or.inr ⟨hv,hgrid,by rw [hai]; exact ⟨t,ht⟩⟩⟩

/-- No two actual source anchored hosts own one undirected Cartesian edge. -/
theorem host_unique (z : Fin (2^r)) {i k : Fin (count (2*count m a) h)} {x y : (VertexPower (VertexPower V a×VertexPower V a) h)×W}
    (hi : Host D he a h r hr hh room hA S ho hb H z i x y)
    (hk : Host D he a h r hr hh room hA S ho hb H z k x y) : i=k := by
  rcases hi with ⟨hw,hi⟩ | ⟨hv,hgi,hi⟩
  · rcases hk with ⟨_,hk⟩ | ⟨hv,_,_⟩
    · exact factorEdge_unique _ hi hk
    · have hg := factorEdge_relation _ hi
      rw [hv] at hg
      exact False.elim ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).loopfree _ hg)
  · rcases hk with ⟨_,hk⟩ | ⟨_,hgk,hk⟩
    · have hg := factorEdge_relation _ hk
      rw [hv] at hg
      exact False.elim ((SourceOrientedFactors.factors D he a h r hr hh room hA S ho hb z).loopfree _ hg)
    · have ha := factorEdge_unique H hi hk
      exact representative_unique D he a h r hr hh room hA S ho hb z i k x.1 ha hgi hgk

theorem host_partition (z : Fin (2^r)) (x y : (VertexPower (VertexPower V a×VertexPower V a) h)×W) :
    ProductRelation (relation (ProductAdjacent (relation R a)) h) T x y ↔
    ∃i : Fin (count (2*count m a) h), Host D he a h r hr hh room hA S ho hb H z i x y ∧
      ∀k : Fin (count (2*count m a) h), Host D he a h r hr hh room hA S ho hb H z k x y→k=i := by
  constructor
  · intro hedge
    obtain ⟨i,hi⟩ := host_cover D he a h r hr hh room hA S ho hb H z hedge
    exact ⟨i,hi,fun _ hk=>host_unique D he a h r hr hh room hA S ho hb H z hk hi⟩
  · rintro ⟨i,hi,_⟩
    exact host_subset D he a h r hr hh room hA S ho hb H z hi

end Host

end Source
#print axioms representative_vertices_unique
#print axioms host_generators_iff
#print axioms host_partition
#print axioms host_unique
#print axioms representative_cover
#print axioms representative_unique
end ErdePaths.SourceHostPartition
