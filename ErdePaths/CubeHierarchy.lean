import ErdePaths.SourceFactors

namespace ErdePaths.CubeHierarchy
open SourceClock SourceFactors HamiltonData HamiltonTower SquareLift

/-- Explicit coordinate transport, with exact actual graph adjacency. -/
structure Coordinates (V : Type) (R : V→V→Prop) (n : Nat) where
  encode : V → Vertex n
  decode : Vertex n → V
  decode_encode : ∀ v, decode (encode v)=v
  encode_decode : ∀ w, encode (decode w)=w
  adjacent : ∀ u v, Adjacent (encode u) (encode v) ↔ R u v

theorem encode_injective {V R n} (I : Coordinates V R n) : Function.Injective I.encode := by
  intro u v h
  simpa only [I.decode_encode] using congrArg I.decode h

def identity (n : Nat) : Coordinates (Vertex n) (@Adjacent n) n where
  encode := fun v => v
  decode := fun v => v
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl
  adjacent := fun _ _ => Iff.rfl

/-- One actual product stage appends literal binary coordinate blocks. -/
def product {V : Type} {R : V→V→Prop} {n : Nat} (I : Coordinates V R n) :
    Coordinates (V×V) (ProductAdjacent R) (n+n) where
  encode := fun v => CubeProduct.encode (I.encode v.1,I.encode v.2)
  decode := fun w => (I.decode (CubeProduct.decode w).1,I.decode (CubeProduct.decode w).2)
  decode_encode v := by simp only [CubeProduct.decode_encode,I.decode_encode]
  encode_decode w := by simp only [I.encode_decode]; exact CubeProduct.encode_decode w
  adjacent u v := by
    rw [CubeProduct.adjacent_iff]
    constructor
    · rintro (⟨h,hr⟩ | ⟨h,hr⟩)
      · exact Or.inr ⟨encode_injective I h,(I.adjacent _ _).mp hr⟩
      · exact Or.inl ⟨encode_injective I h,(I.adjacent _ _).mp hr⟩
    · rintro (⟨h,hr⟩ | ⟨h,hr⟩)
      · exact Or.inr ⟨congrArg I.encode h,(I.adjacent _ _).mpr hr⟩
      · exact Or.inl ⟨congrArg I.encode h,(I.adjacent _ _).mpr hr⟩

def dimension (n : Nat) : Nat→Nat
  | 0 => n
  | k+1 => dimension n k+dimension n k

def tower {V : Type} {R : V→V→Prop} {n : Nat} (I : Coordinates V R n) :
    (k : Nat)→Coordinates (VertexPower V k) (relation R k) (dimension n k)
  | 0 => I
  | k+1 => product (tower I k)

theorem dimension_formula (n k : Nat) : dimension n k=n*2^k := by
  induction k with
  | zero => simp [dimension]
  | succ k ih => simp only [dimension,ih,Nat.pow_succ,Nat.mul_two,Nat.mul_add]

def castCoordinates {V R n d} (eqn : n=d) (I : Coordinates V R n) : Coordinates V R d := by
  subst d; exact I

/-- Coordinate construction for prefix, profile, and upper product stages. -/
def sourceCoordinates (n k h : Nat) :
    Coordinates (VertexPower (VertexPower (Vertex n) k × VertexPower (Vertex n) k) h)
      (relation (ProductAdjacent (relation (@Adjacent n) k)) h)
      (dimension (dimension n k+dimension n k) h) :=
  tower (product (tower (identity n) k)) h

theorem source_dimension (n k h : Nat) :
    dimension (dimension n k+dimension n k) h=n*2^(k+h+1) := by
  rw [dimension_formula,dimension_formula,Nat.pow_add,Nat.pow_add]
  simp only [Nat.pow_one,Nat.mul_add,←Nat.mul_assoc,Nat.mul_two,Nat.add_mul]

/-- Actual hierarchy coordinates at the exact target binary dimension. -/
def sourceIso (n k h : Nat) :
    Coordinates (VertexPower (VertexPower (Vertex n) k × VertexPower (Vertex n) k) h)
      (relation (ProductAdjacent (relation (@Adjacent n) k)) h) (n*2^(k+h+1)) :=
  castCoordinates (source_dimension n k h) (sourceCoordinates n k h)

/-- Transport genuine Hamilton ownership through actual coordinate maps. -/
def transport {V R n m N hN} (I : Coordinates V R n) (D : DecompositionData V R m N hN) :
    DecompositionData (Vertex n) (@Adjacent n) m N hN where
  cycles f := {
    cycle := fun t => I.encode ((D.cycles f).cycle t)
    position := fun w => (D.cycles f).position (I.decode w)
    position_cycle := fun t => by rw [I.decode_encode,(D.cycles f).position_cycle]
    cycle_position := fun w => by rw [(D.cycles f).cycle_position,I.encode_decode]
    adjacent := fun t => (I.adjacent _ _).mpr ((D.cycles f).adjacent t) }
  symmetric := fun _ _ h => adjacent_symm h
  loopfree := fun _ h => adjacent_ne h rfl
  cover u v huv := by
    have hh : R (I.decode u) (I.decode v) := (I.adjacent _ _).mp
      (by simpa only [I.encode_decode] using huv)
    obtain ⟨f,t,ht⟩ := D.cover _ _ hh
    refine ⟨f,t,?_⟩
    have hm := SubdividedWiggle.map_sameEdge I.encode ht
    simpa only [I.encode_decode] using hm
  unique f t g s he := by
    have hh := SubdividedWiggle.map_sameEdge I.decode he
    simp only [I.decode_encode] at hh
    exact D.unique _ _ _ _ hh

/-- Genuine binary-cube Hamilton hierarchy, from genuine initial cube data. -/
noncomputable def cubeFamily {n m e : Nat}
    (D : DecompositionData (Vertex n) (@Adjacent n) m (2^e) (Nat.two_pow_pos e))
    (he : 2≤e) (k h : Nat)
    (S : Fin m → HierarchicalDecode.Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ f a, Profile.cardinality (S f a)%2=1) :
    DecompositionData (Vertex (n*2^(k+h+1))) (@Adjacent (n*2^(k+h+1)))
      (count (2*count m k) h) (lengthPower ((2^(e*2^k))*(2^(e*2^k))) h)
      (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h) :=
  transport (sourceIso n k h) (family D he k h S ho)

/-- Every transported coded factor retains its actual source inverse clock,
with the explicit binary coordinate decoding as its sole change of domain. -/
theorem cube_position {n m e : Nat}
    (D : DecompositionData (Vertex n) (@Adjacent n) m (2^e) (Nat.two_pow_pos e))
    (he : 2≤e) (k h : Nat)
    (S : Fin m → HierarchicalDecode.Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ f a, Profile.cardinality (S f a)%2=1)
    (f : Fin m) (epsilon : Bool) (address : HierarchicalDecode.Address (k+h))
    (v : Vertex (n*2^(k+h+1))) :
    ((cubeFamily D he k h S ho).cycles (index k h f epsilon address)).position v=
      (SourceProfile.clock he (D.cycles f).toClockData k h (S f) (ho f) epsilon address).position
        ((sourceIso n k h).decode v) := by
  change ((family D he k h S ho).cycles (index k h f epsilon address)).position _=_
  exact congrArg (fun C => C.position ((sourceIso n k h).decode v))
    (SourceFactors.clock_eq D he k h S ho f epsilon address)

#print axioms sourceIso
#print axioms cubeFamily
#print axioms cube_position
end ErdePaths.CubeHierarchy
