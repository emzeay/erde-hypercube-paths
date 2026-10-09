import ErdePaths.HamiltonTower
import ErdePaths.SourceProfile

namespace ErdePaths.SourceFactors
open SourceClock SourceProfile HamiltonData HamiltonTower HamiltonSquare Profile HierarchicalDecode SquareLift

/-- Transport only the proved length equality; all graph and ownership data
remain those of the actual input factorization. -/
def castDecomposition {V : Type} {R : V→V→Prop} {m M N : Nat} {hM : 0<M}
    (eqn : M=N) (D : DecompositionData V R m M hM) :
    DecompositionData V R m N (eqn ▸ hM) := by subst N; exact D

theorem castDecomposition_clock {V : Type} {R : V→V→Prop} {m M N : Nat} {hM : 0<M}
    (eqn : M=N) (D : DecompositionData V R m M hM) (f : Fin m) :
    ((castDecomposition eqn D).cycles f).toClockData=castClock eqn (D.cycles f).toClockData := by
  subst N; rfl

/-- Decode actual lower factors into their initial factor and Boolean choices. -/
noncomputable def origin {m : Nat} (k : Nat) (q : Fin (count m k)) : Fin m × Address k :=
  (Classical.choose (code_surjective k q),
    Classical.choose (Classical.choose_spec (code_surjective k q)))

theorem code_origin {m : Nat} (k : Nat) (q : Fin (count m k)) :
    code k (origin k q).1 (origin k q).2=q :=
  Classical.choose_spec (Classical.choose_spec (code_surjective k q))

theorem origin_code {m : Nat} (k : Nat) (f : Fin m) (address : Address k) :
    origin k (code k f address)=(f,address) := by
  obtain ⟨hf,ha⟩ := code_injective k _ _ _ _ (code_origin k (code k f address))
  exact Prod.ext hf ha

noncomputable def prefixFamily {V : Type} {R : V→V→Prop} {m e : Nat}
    (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e) (k : Nat) :
    DecompositionData (VertexPower V k) (relation R k) (count m k) (2^(e*2^k)) (Nat.two_pow_pos _) :=
  castDecomposition (lengthPower_pow e k) (decomposition D
    (by have hp := Nat.pow_le_pow_right (show 1≤2 by decide) he; omega) k)

noncomputable def selectors {m e : Nat} (k : Nat)
    (S : Fin m → Address k → Fin (2^(e*2^k)) → Bool) :
    Fin (count m k) → Fin (2^(e*2^k)) → Bool :=
  fun q => S (origin k q).1 (origin k q).2

theorem selectors_code {m e : Nat} (k : Nat)
    (S : Fin m → Address k → Fin (2^(e*2^k)) → Bool) (f : Fin m) (address : Address k) :
    selectors k S (code k f address)=S f address := by
  unfold selectors
  rw [origin_code]

/-- Actual graph partition after the prefix and fresh profile stage. -/
noncomputable def middle {V : Type} {R : V→V→Prop} {m e : Nat}
    (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e) (k : Nat)
    (S : Fin m → Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ f address, cardinality (S f address)%2=1) :
    DecompositionData (VertexPower V k × VertexPower V k) (ProductAdjacent (relation R k))
      (2*count m k) ((2^(e*2^k))*(2^(e*2^k)))
      (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) :=
  HamiltonProfile.profiles (by have := exponent_bound he k; omega) (prefixFamily D he k)
    (selectors k S) (fun q => ho _ _)

/-- Every upper square retains exact factor/edge-position ownership. -/
noncomputable def family {V : Type} {R : V→V→Prop} {m e : Nat}
    (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e) (k h : Nat)
    (S : Fin m → Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ f address, cardinality (S f address)%2=1) :
    DecompositionData (VertexPower (VertexPower V k × VertexPower V k) h)
      (relation (ProductAdjacent (relation R k)) h) (count (2*count m k) h)
      (lengthPower ((2^(e*2^k))*(2^(e*2^k))) h)
      (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h) :=
  decomposition (middle D he k S ho) (by
    have hp := Nat.two_pow_pos (e*2^k)
    have hh := exponent_bound he k
    have ht := Nat.pow_le_pow_right (show 1≤2 by decide) (show 2≤e*2^k by omega)
    have hm := Nat.mul_le_mul (show 2≤2^(e*2^k) by omega) (show 2≤2^(e*2^k) by omega)
    exact hm) h

/-- Explicit actual index: initial factor, lower source, twin, upper source. -/
def index {m : Nat} (k h : Nat) (f : Fin m) (epsilon : Bool) (address : Address (k+h)) :
    Fin (count (2*count m k) h) :=
  code h (factorIndex (code k f (lowerAddress address),epsilon)) (upperAddress address)

def joinAddress {k h : Nat} (lower : Address k) (upper : Address h) : Address (k+h) :=
  fun i => if hi : i.val<k then lower ⟨i.val,hi⟩ else upper ⟨i.val-k,by have := i.isLt; omega⟩

theorem lower_join {k h : Nat} (lower : Address k) (upper : Address h) :
    lowerAddress (joinAddress lower upper)=lower := by
  funext i
  simp only [lowerAddress,joinAddress,dite_eq_left i.isLt]

theorem upper_join {k h : Nat} (lower : Address k) (upper : Address h) :
    upperAddress (joinAddress lower upper)=upper := by
  funext i
  simp only [upperAddress,joinAddress,dite_eq_right (show ¬k+i.val<k by omega)]
  congr 1
  apply Fin.ext
  change k+i.val-k=i.val
  omega

theorem address_ext {k h : Nat} (a b : Address (k+h))
    (hl : lowerAddress a=lowerAddress b) (hu : upperAddress a=upperAddress b) : a=b := by
  funext i
  by_cases hi : i.val<k
  · exact congrFun hl ⟨i.val,hi⟩
  · have hh := congrFun hu ⟨i.val-k,by have := i.isLt; omega⟩
    have he : (⟨k+(i.val-k),by omega⟩ : Fin (k+h))=i := by
      apply Fin.ext
      change k+(i.val-k)=i.val
      omega
    simpa only [upperAddress,he] using hh

/-- Every owned graph factor has an explicit complete source/profile code. -/
theorem index_surjective {m : Nat} (k h : Nat) (q : Fin (count (2*count m k) h)) :
    ∃ f epsilon address, index k h f epsilon address=q := by
  obtain ⟨mid,upper,hm⟩ := code_surjective h q
  obtain ⟨f,lower,hl⟩ := code_surjective k (factorCoordinates mid).1
  refine ⟨f,(factorCoordinates mid).2,joinAddress lower upper,?_⟩
  simp only [index,lower_join,upper_join]
  rw [hl,factorIndex_coordinates]
  exact hm

/-- Initial factor, source choices, and profile choice retain distinct actual
factor identities; in particular no silently duplicated cycle index occurs. -/
theorem index_injective {m : Nat} (k h : Nat) (f g : Fin m) (epsilon epsilon' : Bool)
    (a b : Address (k+h)) (he : index k h f epsilon a=index k h g epsilon' b) :
    f=g ∧ epsilon=epsilon' ∧ a=b := by
  obtain ⟨hm,hu⟩ := code_injective h _ _ _ _ he
  have hc := congrArg factorCoordinates hm
  simp only [factorCoordinates_index] at hc
  obtain ⟨hf,hl⟩ := code_injective k _ _ _ _ (congrArg Prod.fst hc)
  exact ⟨hf,congrArg Prod.snd hc,address_ext a b hl hu⟩

theorem prefix_clock {V : Type} {R : V→V→Prop} {m e : Nat}
    (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)
    (k : Nat) (f : Fin m) (address : Address k) :
    ((prefixFamily D he k).cycles (code k f address)).toClockData=
      prefixClock (D.cycles f).toClockData k address := by
  unfold prefixFamily
  rw [castDecomposition_clock,HamiltonTower.clock_eq]
  rfl

/-- Lookup is the actual factor clock, including the one genuine profile. -/
theorem clock_eq {V : Type} {R : V→V→Prop} {m e : Nat}
    (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e) (k h : Nat)
    (S : Fin m → Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ f address, cardinality (S f address)%2=1)
    (f : Fin m) (epsilon : Bool) (address : Address (k+h)) :
    ((family D he k h S ho).cycles (index k h f epsilon address)).toClockData=
      clock he (D.cycles f).toClockData k h (S f) (ho f) epsilon address := by
  unfold family index
  rw [HamiltonTower.clock_eq]
  unfold middle
  simp only [HamiltonProfile.profiles,factorCoordinates_index]
  change iteratedClock _ (ProfileLift.clock _
    ((prefixFamily D he k).cycles (code k f (lowerAddress address))).toClockData
    (selectors k S (code k f (lowerAddress address))) _ epsilon) h (upperAddress address)=_
  rw [prefix_clock]
  simp only [selectors_code]
  rfl

#print axioms clock_eq
#print axioms index_surjective
#print axioms index_injective
#print axioms family
#print axioms origin_code
end ErdePaths.SourceFactors
