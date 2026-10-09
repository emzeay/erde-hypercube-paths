import ErdePaths.SourceIsolatedGlobalPaths
import ErdePaths.SourceUniformInput
import ErdePaths.GraphTarget
import ErdePaths.OddClassification

namespace ErdePaths.SourceIsolatedFrontier

private theorem coefficient_bound (R b : Nat) (hR : 3≤R) (hb : b≤2^(R-1)-3) :
    b<2^(R-1) := by
  have hp : 4≤2^(R-1) := Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 2≤R-1)
  omega

private theorem input_short (m R b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hb : b≤2^(R-1)-3) (ho : b%2=1) :
    let I := SourceUniformInput.input m R 1 b hm hR (by decide) (by omega)
      (coefficient_bound R b hR hb) ho
    I.b≤2^(I.a+I.h+1-I.r)-3 := by
  change b≤2^(R-2+1+1-1)-3
  rw [show R-2+1+1-1=R-1 by omega]
  exact hb

private theorem transport {n N L K : Nat} (hn : n=N) (hL : L=K)
    (D : GraphPathDecomposition (Vertex n) (@Adjacent n) L) :
    HasPathDecomposition N K := by
  subst N
  subst K
  exact GraphTarget.to_target D

/-- Unconditional uniform ordinary A=2 frontier. Actual source factors,
chronological isolated neighbors, forks, and full cube edge ownership are
constructed internally; only numeric coefficient restrictions remain. -/
theorem decomposition (m R b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hb : b≤2^(R-1)-3) (ho : b%2=1) :
    HasPathDecomposition (2*m*(2^R+2^(R-1)+b))
      ((2^R+2^(R-1)+b)*2^(2*m*(2^R+2^(R-1)+b)-R-1)) := by
  have hb' := coefficient_bound R b hR hb
  let I := SourceUniformInput.input m R 1 b hm hR (by decide) (by omega) hb' ho
  let t := 2^(2*m*b-1)
  have ht : 0<t := Nat.two_pow_pos _
  have h2 : 2≤t := SourceUniformInput.j_half_ge_two m b hm ho
  have hn : 0<I.m*2^(I.a+I.h+1) := by
    change 0<m*2^(R-2+1+1)
    exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  let n : I.Index := ⟨0,hn⟩
  have hl := SourceUniformInput.length m R 1 b hm hR (by decide) (by omega) hb' ho n
  have hl' := SourceGlobalFold.Input.length_eq I ht n
  have he : SourceGlobalFold.Input.totalLength I t=
      (2^R+2^(R-1)+b)*2^(2*m*(2^R+2^(R-1)+b)-R-1) := hl'.symm.trans hl
  exact transport (SourceUniformInput.dimension m R 1 b hm hR (by decide) (by omega) hb' ho) he
    (SourceIsolatedGlobalPaths.Input.cube I rfl (input_short m R b hm hR hb ho) ht h2
      (SourceUniformInput.jData m b hm ho))

/-- Exact canonical odd frontier, uniformly over arbitrary binary complexity
of the positive odd lower remainder b. -/
theorem frontier (m R b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hb : b≤2^(R-1)-3) (ho : b%2=1) :
    let d := 2^R+2^(R-1)+b
    HasPathDecomposition (2*m*d) (d*2^(2*m*d-d.log2-1)) := by
  dsimp only
  rw [OddClassification.coefficient_log2 (show R-1<R by omega) (coefficient_bound R b hR hb)]
  exact decomposition m R b hm hR hb ho

#print axioms decomposition
#print axioms frontier
end ErdePaths.SourceIsolatedFrontier
