import ErdePaths.SingletonPhaseArc
import ErdePaths.MersenneCodeOrigins

namespace ErdePaths.ZeroUpperCodeOrigins
open SourceClock SourceProfile HierarchicalDecode PairedArc

section Mersenne
variable {e : Nat} (he : 2≤e) (k : Nat) (hk : 2≤k)
  (room : 2^(k+3)∣lengthPower (2^e) k) (exceptional : Bool)

/-- Actual bounded parent phase of the full (possibly duplicate) false code. -/
noncomputable def phase (a : Address k) : Fin (2^(e*2^k)) :=
  ⟨(MersenneCode.code hk exceptional false a).val,by
    have hd : 2^(k+3)∣2^(e*2^k) := by simpa only [lengthPower_pow] using room
    exact Nat.lt_of_lt_of_le (MersenneCode.code hk exceptional false a).isLt
      (Nat.le_of_dvd (Nat.two_pow_pos _) hd)⟩

noncomputable def selectors (a : Address k) : Fin (2^(e*2^k))→Bool := SingletonPhaseArc.selector (phase k hk room exceptional a)

theorem odd (a : Address k) : Profile.cardinality (selectors k hk room exceptional a)%2=1 := by
  unfold selectors
  rw [SingletonPhaseArc.cardinality_one]

/-- Every full code is realized by genuine same-endpoint profile arcs at
ZERO upper depth. The chosen profile depends on its literal source phase. -/
noncomputable def data {V : Type} (C : ClockData V (2^e)) (a : Address k) :
    MersenneCodeOrigins.Data he C k 0 hk (selectors k hk room exceptional)
      (odd k hk room exceptional) exceptional a := by
  have hp : 1≤e*2^k := by have := SourceProfile.exponent_bound he k; omega
  let c := phase k hk room exceptional a
  let P := SingletonPhaseArc.lifted hp (prefixClock C k a) c false
  let Q := SingletonPhaseArc.lifted hp (prefixClock C k a) c true
  have hd : 2^(k+3)∣2^(e*2^k) := by simpa only [lengthPower_pow] using room
  have hc : c.val=(MersenneCode.code hk exceptional false a).val := rfl
  have hs := (SingletonPhaseArc.lifted_phases hp hd (prefixClock C k a) c false).1
  have ht := (SingletonPhaseArc.lifted_phases hp hd (prefixClock C k a) c true).2
  refine { arcFalse:=P, arcTrue:=Q, start_equal:=?_, end_equal:=?_, false_code:=?_, true_code:=?_ }
  · rw [SingletonPhaseArc.lifted_start,SingletonPhaseArc.lifted_start]
  · rw [SingletonPhaseArc.lifted_endpoint,SingletonPhaseArc.lifted_endpoint]
  · exact hs.trans (by rw [hc]; exact Nat.mod_eq_of_lt (MersenneCode.code hk exceptional false a).isLt)
  · exact ht.trans (by rw [hc]; exact MersenneCodeOrigins.endpoint_phase hk exceptional a)

end Mersenne
#print axioms data
end ErdePaths.ZeroUpperCodeOrigins
