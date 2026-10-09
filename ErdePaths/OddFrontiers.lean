import ErdePaths.OddClassification
import ErdePaths.PowerFrontier
import ErdePaths.TwoBitFrontier
import ErdePaths.SourceUniformPaths
import ErdePaths.SourceIsolatedFrontier
import ErdePaths.MersenneUniformPaths
import ErdePaths.SevenFrontier
import ErdePaths.FifteenFrontier

namespace ErdePaths.OddFrontiers

/-- Every positive odd coefficient, with unrestricted binary complexity and
dimension multiplier, has its actual canonical simple-path frontier. -/
theorem frontiers (m d : Nat) (hm : 1≤m) (hd : 0<d) (ho : d%2=1) :
    HasPathDecomposition (2*m*d) (d*2^(2*m*d-d.log2-1)) := by
  rcases OddClassification.classify hd ho with h1 | htwo | hmany
  · subst d
    simp only [show (1:Nat).log2=0 by decide,Nat.sub_zero,Nat.mul_one,Nat.one_mul]
    exact PowerFrontier.frontier m hm
  · obtain ⟨R,hR,rfl,hlog⟩ := htwo
    rw [hlog]
    exact TwoBitFrontier.frontier m R hm hR
  · obtain ⟨R,s,b,hs,hsR,hbpos,hb,hbo,hde,hlog⟩ := hmany
    by_cases hsmall : R<3
    · have hseven := (OddClassification.small_ordinary hs hsR hb hbo hsmall).2.2.2
      rw [hde,hseven]
      exact SevenFrontier.frontier m hm
    · have hR : 3≤R := by omega
      rcases OddClassification.opening_split hsR hb hbo with hbuffer | hshort | hcomplement
      · have hrs : R-(R-s)=s := by omega
        have hf := SourceUniformPaths.frontier m R (R-s) b hm hR hbuffer
          (show R-s<R by omega) (by simpa only [hrs] using hb) hbo
        dsimp only at hf
        rw [hrs] at hf
        simpa only [←hde] using hf
      · obtain ⟨hr,hbshort⟩ := hshort
        have hsEq : s=R-1 := by omega
        subst s
        have hf := SourceIsolatedFrontier.frontier m R b hm hR hbshort hbo
        dsimp only at hf
        simpa only [←hde] using hf
      · obtain ⟨hr,hbcomplement⟩ := hcomplement
        have hs1 : s+1=R := by omega
        have hpow : 2^R=2^s*2 := by rw [←hs1,Nat.pow_succ]
        have hdM : d=2^(R+1)-1 := by
          rw [Nat.pow_succ]
          have hp := Nat.two_pow_pos s
          omega
        by_cases hroom : 4≤R
        · have hf := MersenneUniformPaths.frontier m R hm hroom
          dsimp only at hf
          simpa only [←hdM] using hf
        · have hfifteen := (OddClassification.small_mersenne hR (by omega)).2
          rw [hdM,hfifteen]
          exact FifteenFrontier.frontier m hm

#print axioms frontiers
end ErdePaths.OddFrontiers
