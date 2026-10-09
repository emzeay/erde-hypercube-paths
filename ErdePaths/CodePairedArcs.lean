import ErdePaths.SourcePairedArcs
import ErdePaths.DenseCodeTwins

namespace ErdePaths.CodePairedArcs
open SourceClock SourceProfile PairedArc HierarchicalDecode

/-- Genuine source arcs prescribe the literal false code at their shared
start and the literal true code at their shared end. This constructs the
physical occurrences needed by opposed AAC origins for every source address. -/
theorem exists_pair {V : Type} {e u : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
    (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
    (address : Address (a+h))
    (hbalance : Profile.prefixCount (S (lowerAddress address)) (2*u)=u) :
    ∃q : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
        (SourceProfile.clock he C a h S ho false address) (2*u),
    ∃q' : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
        (SourceProfile.clock he C a h S ho true address) (2*u),
      q.vertex ⟨0,by omega⟩=q'.vertex ⟨0,by omega⟩ ∧
      q.vertex ⟨2*u,by omega⟩=q'.vertex ⟨2*u,by omega⟩ ∧
      ((SourceProfile.clock he C a h S ho false address).position (q.vertex ⟨0,by omega⟩)).val%(2^(a+h+1))=
        (DenseSourceMarks.code r hr false address).val ∧
      ((SourceProfile.clock he C a h S ho true address).position (q'.vertex ⟨2*u,by omega⟩)).val%(2^(a+h+1))=
        (DenseSourceMarks.code r hr true address).val := by
  have hshort : 2*u<2^(a+h+1) := by
    rw [hA]
    exact Nat.pow_lt_pow_right (by decide) hr
  let c := DenseSourceMarks.code r hr false address
  obtain ⟨q,q',hs,he',hp⟩ := SourcePairedArcs.paired he (Nat.two_pow_pos _) C a h hh room hshort
    S ho address hbalance c
  refine ⟨q,q',hs,he',?_,?_⟩
  · have hz := (hp ⟨0,by omega⟩).1
    simpa only [Nat.add_zero,Nat.mod_eq_of_lt c.isLt,c] using hz
  · have hz := (hp ⟨2*u,by omega⟩).2
    have hc : (c.val+2*u)%(2^(a+h+1))=(DenseSourceMarks.code r hr true address).val := by
      rw [hA]
      exact DenseCodeTwins.code_endpoint_phase r hr address
    exact hz.trans hc

#print axioms exists_pair
end ErdePaths.CodePairedArcs
