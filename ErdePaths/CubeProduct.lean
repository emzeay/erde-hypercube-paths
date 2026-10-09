import ErdePaths.Binary
import ErdePaths.AnchoredEmbedding

namespace ErdePaths.CubeProduct
open SquareLift AnchoredEmbedding

/-- Append the second block's bits above the first block's bits. -/
def encode {n m : Nat} (u : Vertex n × Vertex m) : Vertex (n+m) :=
  ⟨2^n*u.2.val+u.1.val,by
    have hm := Nat.mul_le_mul_left (2^n) (show u.2.val+1≤2^m by have := u.2.isLt; omega)
    rw [Nat.mul_add,Nat.mul_one,←Nat.pow_add] at hm
    have := u.1.isLt
    omega⟩

def decode {n m : Nat} (w : Vertex (n+m)) : Vertex n × Vertex m :=
  (⟨w.val%(2^n),Nat.mod_lt _ (Nat.two_pow_pos n)⟩,
   ⟨w.val/(2^n),by
      have hw : w.val<2^n*2^m := by simpa only [Nat.pow_add] using w.isLt
      exact Nat.div_lt_of_lt_mul hw⟩)

theorem encode_decode {n m : Nat} (w : Vertex (n+m)) : encode (decode w)=w := by
  apply Fin.ext
  exact Nat.div_add_mod w.val (2^n)

theorem decode_encode {n m : Nat} (u : Vertex n × Vertex m) : decode (encode u)=u := by
  apply Prod.ext <;> apply Fin.ext
  · simp only [decode,encode,Nat.mul_add_mod,Nat.mod_eq_of_lt u.1.isLt]
  · simp only [decode,encode]
    rw [Nat.mul_add_div (Nat.two_pow_pos n),Nat.div_eq_of_lt u.1.isLt,Nat.add_zero]

theorem encode_injective {n m : Nat} : Function.Injective (@encode n m) := by
  intro u v he
  have hh := congrArg decode he
  simpa only [decode_encode] using hh

theorem encode_surjective {n m : Nat} : Function.Surjective (@encode n m) :=
  fun w => ⟨decode w,encode_decode w⟩

theorem bit_left {n m : Nat} (u : Vertex n × Vertex m) (i : Fin n) :
    binaryTuple (encode u) (Fin.castAdd m i)=binaryTuple u.1 i := by
  simp only [binaryTuple,encode,Fin.castAdd,Fin.castLE]
  rw [Nat.testBit_two_pow_mul_add _ u.1.isLt]
  exact ite_eq_left i.isLt

theorem bit_right {n m : Nat} (u : Vertex n × Vertex m) (i : Fin m) :
    binaryTuple (encode u) (Fin.natAdd n i)=binaryTuple u.2 i := by
  simp only [binaryTuple,encode,Fin.natAdd]
  rw [Nat.testBit_two_pow_mul_add _ u.1.isLt,ite_eq_right (by omega : ¬n+i.val<n)]
  congr 1
  omega

theorem bit_left_raw {n m : Nat} (u : Vertex n × Vertex m) (i : Fin n) :
    (encode u).val.testBit (Fin.castAdd m i).val=u.1.val.testBit i.val := bit_left u i

theorem bit_right_raw {n m : Nat} (u : Vertex n × Vertex m) (i : Fin m) :
    (encode u).val.testBit (Fin.natAdd n i).val=u.2.val.testBit i.val := bit_right u i

private theorem left_ne_right {n m : Nat} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i≠Fin.natAdd n j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=n+j.val at hv
  have := i.isLt
  omega

/-- The actual integer-encoded cube is exactly its Cartesian coordinate product. -/
theorem adjacent_iff {n m : Nat} (u v : Vertex n × Vertex m) :
    Adjacent (encode u) (encode v) ↔ ProductRelation (@Adjacent n) (@Adjacent m) u v := by
  constructor
  · rintro ⟨d,hd,hi⟩
    have hcoords : ∀ i : Fin (n+m), i≠d → (encode u).val.testBit i.val=(encode v).val.testBit i.val := hi
    revert hd hcoords
    refine Fin.addCases (fun d => ?_) (fun d => ?_) d
    · intro hd hcoords
      refine Or.inl ⟨?_,d,?_,?_⟩
      · apply binaryTuple_injective
        funext j
        have hh := hcoords (Fin.natAdd n j) (Ne.symm (left_ne_right d j))
        simpa only [bit_right_raw,binaryTuple] using hh
      · simpa only [bit_left_raw] using hd
      · intro i hne
        have hcast : Fin.castAdd m i≠Fin.castAdd m d := by
          intro he
          have hv : i.val=d.val := congrArg (fun x : Fin (n+m) => x.val) he
          exact hne (Fin.ext hv)
        simpa only [bit_left_raw] using hcoords (Fin.castAdd m i) hcast
    · intro hd hcoords
      refine Or.inr ⟨?_,d,?_,?_⟩
      · apply binaryTuple_injective
        funext j
        have hh := hcoords (Fin.castAdd m j) (left_ne_right j d)
        simpa only [bit_left_raw,binaryTuple] using hh
      · simpa only [bit_right_raw] using hd
      · intro i hne
        have hcast : Fin.natAdd n i≠Fin.natAdd n d := by
          intro he
          have hv := congrArg Fin.val he
          exact hne (Fin.ext (by change n+i.val=n+d.val at hv; omega))
        simpa only [bit_right_raw] using hcoords (Fin.natAdd n i) hcast
  · rintro (⟨hm,d,hd,hi⟩ | ⟨hn,d,hd,hi⟩)
    · refine ⟨Fin.castAdd m d,?_,?_⟩
      · simpa only [bit_left_raw] using hd
      · intro i hne
        revert hne
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · intro hne
          have hj : j≠d := by intro he; exact hne (congrArg (Fin.castAdd m) he)
          simpa only [bit_left_raw] using hi j hj
        · intro hne
          rw [bit_right_raw,bit_right_raw,hm]
    · refine ⟨Fin.natAdd n d,?_,?_⟩
      · simpa only [bit_right_raw] using hd
      · intro i hne
        revert hne
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · intro hne
          rw [bit_left_raw,bit_left_raw,hn]
        · intro hne
          have hj : j≠d := by intro he; exact hne (congrArg (Fin.natAdd n) he)
          simpa only [bit_right_raw] using hi j hj

#print axioms encode_injective
#print axioms encode_surjective
#print axioms adjacent_iff
end ErdePaths.CubeProduct
