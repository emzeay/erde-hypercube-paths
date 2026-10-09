import ErdePaths.CubeProduct
import ErdePaths.AACUnfold
import ErdePaths.HamiltonData

namespace ErdePaths.CubeParity

/-- Physical bipartition: XOR of the actual binary coordinates. -/
def tupleParity : {n : Nat} → (Fin n → Bool) → Bool
  | 0,_ => false
  | n+1,f => tupleParity (fun i : Fin n => f i.castSucc) ^^ f (Fin.last n)

def parity {n : Nat} (v : Vertex n) : Bool := tupleParity (binaryTuple v)

private theorem xor_not_left (a b : Bool) : (!a ^^ b)= !(a ^^ b) := by
  cases a <;> cases b <;> rfl
private theorem xor_not_right (a b : Bool) : (a ^^ !b)= !(a ^^ b) := by
  cases a <;> cases b <;> rfl

/-- Exactly one changed coordinate flips the genuine physical bipartition. -/
theorem tuple_flip {n : Nat} (f g : Fin n → Bool) (d : Fin n)
    (hd : f d≠g d) (he : ∀ i, i≠d → f i=g i) : tupleParity g= !tupleParity f := by
  induction n with
  | zero => exact Fin.elim0 d
  | succ n ih =>
    revert hd he
    refine Fin.lastCases (fun hd he => ?_) (fun d hd he => ?_) d
    · have hlower : (fun i : Fin n => f i.castSucc)=(fun i => g i.castSucc) := by
        funext i
        exact he i.castSucc (by intro hh; have hh' := congrArg Fin.val hh; have := i.isLt; simp at hh'; omega)
      have hlast : g (Fin.last n)= !f (Fin.last n) := by
        cases hf : f (Fin.last n) <;> cases hg : g (Fin.last n) <;> simp_all
      simp only [tupleParity,hlower,hlast,xor_not_right]
    · have hlast : f (Fin.last n)=g (Fin.last n) := by
        apply he
        intro hh
        have hv := congrArg Fin.val hh
        have := d.isLt
        simp at hv
        omega
      have hp := ih (fun i => f i.castSucc) (fun i => g i.castSucc) d hd (by
        intro i hn
        exact he i.castSucc (fun hh => hn (Fin.castSucc_inj.mp hh)))
      simp only [tupleParity,hp,←hlast,xor_not_left]

theorem adjacent_flips {n : Nat} {u v : Vertex n} (h : Adjacent u v) : parity v= !parity u := by
  obtain ⟨d,hd,he⟩ := h
  exact tuple_flip (binaryTuple u) (binaryTuple v) d hd he

/-- Physical parity along every actual cube path clock, without a free
coloring assumption. Its phase is fixed by the clock's actual origin. -/
theorem clock_parity {n N : Nat} (hN : 0<N) (C : HamiltonData.CycleData (Vertex n) (@Adjacent n) N hN)
    (t : Fin N) : parity (C.cycle t)=PairedLayers.flipN t.val (parity (C.cycle ⟨0,hN⟩)) := by
  have hh : ∀ k (hk : k<N), parity (C.cycle ⟨k,hk⟩)=
      PairedLayers.flipN k (parity (C.cycle ⟨0,hN⟩)) := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k<N := by omega
      have hs : SquareLift.successor hN (⟨k,hk'⟩ : Fin N)=⟨k+1,hk⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hk)
      have hp := adjacent_flips (C.adjacent ⟨k,hk'⟩)
      rw [hs,ih hk'] at hp
      rw [PairedLayers.flipN,PairedLayers.flipN_not]
      exact hp
  exact hh t.val t.isLt

theorem tuple_false (n : Nat) : tupleParity (fun _ : Fin n => false)=false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [tupleParity,ih] using Bool.xor_false false

theorem zero_parity (n : Nat) : parity (⟨0,Nat.two_pow_pos n⟩ : Vertex n)=false := by
  change tupleParity (fun i : Fin n => (0 : Nat).testBit i.val)=false
  have hf : (fun i : Fin n => (0 : Nat).testBit i.val)=(fun _ => false) := by
    funext i
    simp
  rw [hf]
  exact tuple_false n

/-- Splitting the actual physical binary word splits its bipartition XOR. -/
theorem tuple_split (n m : Nat) (f : Fin (n+m) → Bool) :
    tupleParity f =
      (tupleParity (fun i : Fin n => f (Fin.castAdd m i)) ^^
        tupleParity (fun j : Fin m => f (Fin.natAdd n j))) := by
  induction m with
  | zero =>
    have he : (fun i : Fin n => f (Fin.castAdd 0 i))=f := by
      funext i
      rfl
    simp only [tupleParity,Bool.xor_false,he]
  | succ m ih =>
    change (tupleParity (fun i : Fin (n+m) => f i.castSucc) ^^ f (Fin.last (n+m)))=_
    rw [ih]
    have hl : (fun i : Fin n => f ((Fin.castAdd m i).castSucc))=
        (fun i => f (Fin.castAdd (m+1) i)) := by funext i; rfl
    have hr : (fun j : Fin m => f ((Fin.natAdd n j).castSucc))=
        (fun j => f (Fin.natAdd n j.castSucc)) := by funext j; rfl
    have ht : f (Fin.last (n+m))=f (Fin.natAdd n (Fin.last m)) := by
      rfl
    rw [hl,hr,ht]
    exact Bool.xor_assoc _ _ _

theorem product_parity {n m : Nat} (u : Vertex n×Vertex m) :
    parity (CubeProduct.encode u)=(parity u.1 ^^ parity u.2) := by
  unfold parity
  rw [tuple_split n m]
  have hl : (fun i : Fin n => binaryTuple (CubeProduct.encode u) (Fin.castAdd m i))=binaryTuple u.1 := by
    funext i
    exact CubeProduct.bit_left u i
  have hr : (fun j : Fin m => binaryTuple (CubeProduct.encode u) (Fin.natAdd n j))=binaryTuple u.2 := by
    funext j
    exact CubeProduct.bit_right u j
  rw [hl,hr]

#print axioms product_parity
#print axioms adjacent_flips
#print axioms clock_parity
end ErdePaths.CubeParity
