import ErdePaths.OriginFactors
import ErdePaths.QuarterPhysicalIncidence

namespace ErdePaths.QuarterFactorGeometry
open SourceClock SourceProfile HamiltonData HamiltonTower HierarchicalDecode SquareLift
attribute [local instance] Classical.propDecidable

variable {V : Type} {R : V→V→Prop} {m e : Nat}
  (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)

/-- Actual quarter factor clock and true physical-incidence clock coincide. -/
theorem clock_eq (f : Fin m) (epsilon : Bool) (a : Address 1) :
    ((OriginFactors.Quarter.factors D he (⟨1,by decide⟩ : Fin 2)).cycles
      (SourceFactors.index 1 0 f epsilon a)).toClockData=
      QuarterPhysicalIncidence.oriented he (D.cycles f).toClockData epsilon a := by
  rw [OriginFactors.Quarter.factors,OriginFactors.clock_eq]
  cases epsilon <;> rfl

section Host
variable {W : Type} {T : W→W→Prop} {B : Nat} {hB : 0<B}
  (H : DecompositionData W T (m*(2*2^(1-1))) B hB)

noncomputable def Host (z : Fin 2) (i : Fin (2*count m 1))
    (x y : (VertexPower V 1×VertexPower V 1)×W) : Prop :=
  OriginFactors.Host D he 1 0 (by decide)
    (fun _=>QuarterProfileOrigins.selectors he) (fun _=>QuarterProfileOrigins.odd he)
    (fun f=>QuarterSourceOrigins.data he (D.cycles f).toClockData) H z i x y

theorem host_partition (z : Fin 2) (x y : (VertexPower V 1×VertexPower V 1)×W) :
    AnchoredEmbedding.ProductRelation (ProductAdjacent (relation R 1)) T x y ↔
      ∃i : Fin (2*count m 1), Host D he H z i x y ∧
        ∀i',Host D he H z i' x y→i'=i :=
  OriginFactors.host_partition D he 1 0 (by decide)
    (fun _=>QuarterProfileOrigins.selectors he) (fun _=>QuarterProfileOrigins.odd he)
    (fun f=>QuarterSourceOrigins.data he (D.cycles f).toClockData) H z x y

/-- Actual retained geometric host equals the owned zero-upper source host. -/
theorem grid_host_iff (z : Fin 2) (i : Fin (2*count m 1))
    (x y : (VertexPower V 1×VertexPower V 1)×W) :
    SourceAACBase.GridHost (Nat.two_pow_pos (e*2^(1+1)-1)) (by decide : 0<2) hB
      ((OriginFactors.Quarter.factors D he z).cycles i).toClockData
      ((H.cycles (OriginFactors.association 1 0 (by decide) i)).toClockData) x y ↔
    Host D he H z i x y := by
  let Gc:=(OriginFactors.Quarter.factors D he z).cycles i
  let J:=H.cycles (OriginFactors.association 1 0 (by decide) i)
  change _ ↔ ((x.2=y.2 ∧ ∃t,SameEdge (Gc.cycle t,Gc.cycle (successor (Nat.mul_pos (Nat.two_pow_pos _) (by decide : 0<2)) t)) (x.1,y.1)) ∨
      (x.1=y.1 ∧ (Gc.position x.1).val%2=0 ∧
        ∃j,SameEdge (J.cycle j,J.cycle (successor hB j)) (x.2,y.2)))
  constructor
  · rintro ⟨label,hl⟩
    cases label with
    | inl p =>
      have hv : x.2=y.2 := by
        rcases hl with hl|hl
        · exact (congrArg (fun e=>e.1.2) hl).symm.trans (congrArg (fun e=>e.2.2) hl)
        · exact (congrArg (fun e=>e.2.2) hl).symm.trans (congrArg (fun e=>e.1.2) hl)
      exact Or.inl ⟨hv,p.1,SubdividedWiggle.map_sameEdge Prod.fst hl⟩
    | inr p =>
      have hv : x.1=y.1 ∧ Gc.cycle (AnchoredEmbedding.positionEncode p.1 ⟨0,by decide⟩)=x.1 := by
        rcases hl with hl|hl
        · exact ⟨(congrArg (fun e=>e.1.1) hl).symm.trans (congrArg (fun e=>e.2.1) hl),congrArg (fun e=>e.1.1) hl⟩
        · exact ⟨(congrArg (fun e=>e.2.1) hl).symm.trans (congrArg (fun e=>e.1.1) hl),congrArg (fun e=>e.2.1) hl⟩
      exact Or.inr ⟨hv.1,(SourceAnchorCoordinates.anchor_vertices_iff (by decide : 0<2) Gc.toClockData x.1).mp ⟨p.1,hv.2⟩,
        p.2,SubdividedWiggle.map_sameEdge Prod.snd hl⟩
  · rintro (⟨hw,t,ht⟩ | ⟨hv,hgrid,j,hj⟩)
    · refine ⟨.inl (t,J.position x.2),?_⟩
      have hem:=SubdividedWiggle.map_sameEdge (fun v=>(v,x.2)) ht
      change SameEdge ((Gc.cycle t,J.cycle (J.position x.2)),
        (Gc.cycle (successor (Nat.mul_pos (Nat.two_pow_pos _) (by decide : 0<2)) t),J.cycle (J.position x.2))) (x,y)
      rw [J.cycle_position]
      have hx : (x.1,y.2)=x:=Prod.ext rfl hw.symm
      simpa only [hw,Prod.eta,hx] using hem
    · obtain ⟨column,hcolumn⟩ := (SourceAnchorCoordinates.anchor_vertices_iff (by decide : 0<2) Gc.toClockData x.1).mpr hgrid
      refine ⟨.inr (column,j),?_⟩
      have hem:=SubdividedWiggle.map_sameEdge (fun w=>(x.1,w)) hj
      change SameEdge ((Gc.cycle (AnchoredEmbedding.positionEncode column ⟨0,by decide⟩),J.cycle j),
        (Gc.cycle (AnchoredEmbedding.positionEncode column ⟨0,by decide⟩),J.cycle (successor hB j))) (x,y)
      rw [hcolumn]
      have hx : (y.1,x.2)=x:=Prod.ext hv.symm rfl
      simpa only [hv,Prod.eta,hx] using hem

/-- Literal actual zero-upper quarter-word Euler base, using genuine factors. -/
noncomputable def sourceBase (z : Fin 2) (i : Fin (2*count m 1)) :
    Fin (2^(e*2^(1+1)-1)*B*(2+1))→(VertexPower V 1×VertexPower V 1)×W :=
  SourceAACBase.base (Nat.two_pow_pos _) (by decide : 0<2) hB
    (QuarterPatternGeometry.euler (Nat.two_pow_pos _) hB (QuarterPhysicalIncidence.period he))
    ((OriginFactors.Quarter.factors D he z).cycles i).toClockData
    ((H.cycles (OriginFactors.association 1 0 (by decide) i)).toClockData)

/-- Exact successive-edge ledger for the actual zero-upper physical base.
This supplies the real AAC host input; no traversal/host-cover premise. -/
theorem source_host_iff (z : Fin 2) (i : Fin (2*count m 1))
    (x y : (VertexPower V 1×VertexPower V 1)×W) :
    Host D he H z i x y ↔
      ∃n : Fin (2^(e*2^(1+1)-1)*B*(2+1)), SameEdge
        (sourceBase D he H z i n,
         sourceBase D he H z i
           (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) n)) (x,y) := by
  rw [←grid_host_iff D he H z i]
  exact SourceAACBase.gridHost_iff (Nat.two_pow_pos _) (by decide : 0<2) hB
    (QuarterPatternGeometry.euler (Nat.two_pow_pos _) hB (QuarterPhysicalIncidence.period he)) _ _ x y

end Host
#print axioms clock_eq
#print axioms host_partition
#print axioms source_host_iff
end ErdePaths.QuarterFactorGeometry
