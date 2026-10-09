# Proof of the even-hypercube path-decomposition statement

This is the mathematical exposition accompanying the Lean formalization of Conjecture 8 in Joshua Erde’s [*Decomposing the cube into paths*, arXiv:1310.6776v1, §3](https://arxiv.org/pdf/1310.6776v1#page=7). It is a provisional research manuscript. Independent mathematical review has not been completed.

**AI disclosure.** This document is an AI-generated prose argument explaining the formal proof, research for which was also conducted with the help of AI. Lean’s kernel checks the formalization. I plan to release a revised proof exposition with more of my own mathematical development and writing in the future.

## Statement and conventions

For every even integer n≥2 and integer ℓ≥1 with ℓ<2^n and ℓ dividing n·2^(n−1), the edges of the binary cube Q_n partition into simple paths of exactly ℓ edges. Paths may share vertices. A simple path has no repeated vertex; edges are undirected.

The formal proof is complete source code in `ErdePaths/`, concluding in [Conjecture.lean](ErdePaths/Conjecture.lean). The exposition below explains its uniform construction. Detailed local statements and their proofs are in the linked Lean modules; no external research notes or experimental certificates are needed to check the theorem. The final section maps the argument to those modules.

The Hamilton decomposition of every even cube is an established mathematical input: Q_(2m) has m Hamilton cycles, each of length 2^(2m). The formalization proves it internally in [EvenHamilton.lean](ErdePaths/EvenHamilton.lean), rather than assuming it.

A cycle **clock** identifies its vertices with cyclic positions; an **anchor** selects positions spaced by a fixed power of two. A **profile** chooses the positive direction followed at each height of a square torus. An **alternating anchored circuit (AAC)** is the transition construction on an anchored product described in §4. Its **marks** are the unique internal vertices where its interval color changes. Binary **source addresses** record square-factor choices. All coordinates and congruences below refer to actual cycle clocks, so the construction must establish physical edge ownership as well as numerical counts.

Natural-number exponents and remainders in the Lean files have their ordinary integer meaning under the bounds proved alongside each use. The exponent r of the highest binary bit used below is called R in the numerical frontier interfaces; their parameter r is the exponent of A.

## 1. Reduction to one maximal length for each odd divisor

Write ℓ=d·2^b with d odd. Divisibility implies d divides n, since d is coprime to 2^(n−1). As n is even, n=2md for an integer m≥1. Put r=⌊log₂d⌋. Then

    2^r≤d<2^(r+1),     b≤n−r−1.

The second inequality follows from ℓ<2^n. The exponent n−r−1 is nonnegative: d≤n and n≥2 imply r≤n−1. Set

    M_d=d·2^(n−r−1).

This length is strictly less than 2^n, divides n·2^(n−1) with quotient 2m·2^r, and is divisible by ℓ. An ordered simple M_d-path can be cut into consecutive ℓ-edge segments; these remain simple and partition its edges. Thus it suffices to construct paths of length M_d for every odd d and n=2md.

For d=1, cut the Hamilton cycles of Q_n into their two equal halves. This gives length 2^(n−1), including the four-cycle Q_2. Subdivision handles every smaller admissible power of two.

## 2. Standard square factors and hierarchical representative decoding

A Hamilton cycle of even length N on X identifies its torus product with C_N□C_N. The standard two diagonal factors have actual cyclic index formulas

    I₊(i,j)=iN+(i−j mod N),
    I₋(i,j)=(−j mod N)N+(i−j mod N).

They are Hamilton cycles and partition the torus edges. If D divides N, both indices reduce to i−j modulo D. All cycle indices here begin at the common physical zero. Repeated squaring of each original factor E_t partitions the cube of doubled dimension at each stage: every coordinate edge has its unique parent factor owner, and both child factors partition its torus.

After j squarings from Q_(2m), the parent cycle length is

    N_j=2^(2m·2^j).

Whenever N_j is divisible by 2^(p+1), both branch choices have the same reduced index through bit p. Later squarings preserve that equality. Therefore, if source branch j is assigned address bit p(j), and 2m·2^j≥p(j)+1, every final clock extending a fixed earlier source prefix agrees through the bit being selected, independently of its undecided suffix.

Decode one bit at a time: an equality between a factor's physical clock and its assigned address plus a fixed shift selects exactly one branch at each source position. Positions assigned to upper configuration bits complete the address freely once the source is fixed. Strict prefix independence supplies existence and uniqueness; agreement of two shifts in their low a+1 bits makes their decoded addresses agree through the same bits. No common fine clock across all factors is needed.

## 3. Odd parts with two binary ones

Let d=P+1, P=2^r, r≥1. Apply r standard squarings to each E_t of Q_(2m), producing P Hamilton factors of G=Q_(2mP). Assign source branch j to address bit j. The inequality 2m·2^j≥j+1 holds for every j≥0, so the decoding in §2 gives, at every physical G vertex, exactly one factor with actual index congruent to its address modulo P.

These cyclic residue sets partition V(G) within each t-group and have spacing P along their cycles. Pair each such group with E_t on H=Q_(2m), represented by every H vertex. The anchored products have all G-direction cycle edges at every H vertex, and H-direction cycle edges precisely at the selected G representatives. They partition G□H edges by the two unique owners.

Each product is a rectangular torus with first-axis subdivision P, underlying lengths 2^(2mP−r) and 2^(2m), both even and at least 4. The explicit balanced two-wiggle gives two simple equal cycles. At an anchor its two nearest first-axis interior neighbors belong exclusively to opposite cycles: they are distinct degree-two vertices, since P≥2. Exchange those two incident edges to open both cycles into simple paths. The anchored product has (1+1/P)·2^n edges, so each path has length

    (P+1)·2^(n−r−1)=M_d.

There are 2mP paths. This argument uses only the Hamilton input and the explicit square/two-wiggle/fork lemmas; a separate DR-splittable existence theorem is unnecessary.

## 4. The common pipeline for higher binary weight

Every remaining odd d has a unique representation

    d=P+L+b,     P=2^r>L=2^s≥2,     1≤b<L odd,
    A=P/L.

Use coordinate blocks G=Q_(2mP), H=Q_(2mL), J=Q_(2mb). For each original t, construct P Hamilton factors of G arranged into L old groups of A factors. Each old group must have spacing-A representatives partitioning V(G). Assign the L H Hamilton factors in its t-block to these old groups, representing every H vertex. The resulting anchored products partition G□H edges. Their underlying torus has first-axis subdivision A and lengths

    K₀=2^(2mP)/A,     B=2^(2mL).

Write C=|V(G□H)|. Their edges number E=(A+1)C/A. The actual patterns below have periods 2L or 4L; both divide K₀ because 2mP≥r+2, so 2mP−log₂A≥log₂L+2.

### Alternating anchored circuits

On the underlying torus use a balanced periodic binary turn pattern independent of the H row. At each grid vertex the turn pairs each vertical direction with a horizontal direction. Horizontal edges receive alternating row colors. A subdivided vertical interval has one internal color change exactly when its neighboring turn bits agree; that internal degree-two vertex is its mark. Unmarked degree-two vertices have a constant color. Each grid vertex has one transition visit of each color.

For any balanced turn pattern, the transition invariant b₀=σ(−1)^(turn) (σ denotes horizontal H traversal direction) makes the first coordinate advance by a fixed unit and gives zero net H displacement after K₀ macros. Hence there are B baseline unoriented circuits. When turn_(−1)=1 and turn₀=turn₁=0, flipping column 0 in every H row except the last merges consecutive circuit labels in a chain, leaving exactly one Euler circuit. Each flip replaces one interval 0 mark by one interval −1 mark, a displacement A along the G cycle.

Index every H factor so its last vertex is the same physical h*. If two G factors share literal forward A-edge endpoints c,c+A, reverse the c-owner and keep the c+A-owner forward. Their surgeries exchange the same two physical endpoints at every H vertex except h*. Thus paired surgery preserves global pointwise mark multiplicity, even when the factors use different H cycles.

Marks are distinct degree-two vertices and are visited once. Grid vertices occur twice, once in each color, hence in Euler intervals of opposite mark parity. These are the exact hypotheses for simple folded outputs.

### Noncrossing labels and two cycles

For each initial Hamilton index, the marks below cover each physical G□H vertex exactly b times. Aggregating all m initial indices gives multiplicity mb. Each individual AAC has balanced physical marked parity: its G marks have constant parity, its baseline mark count is the same in every H row, and the surgery moves a mark by the even distance A within one row. The H cycle has equal numbers of rows of each physical parity.

A balanced cyclic binary mark word admits a noncrossing perfect matching joining opposite physical parities: recursively remove adjacent opposite symbols. Chords are nested or disjoint. Their union over all AACs is an mb-regular bipartite multigraph on physical G□H vertices, with no loops. Counting incident edges proves Hall's condition; remove perfect matchings successively. Assign the mb Hamilton factors of J=Q_(2mb) as matching labels. Every physical base vertex receives every label exactly once.

For each AAC, form cyclic mark layers on X=V(J), with the assigned label's actual Hamilton cycle as vertical edges in its layer. Color horizontal edges (j,x)—(j+1,x) by χ_J(x)+j+1 modulo 2. Split each vertical label cycle into alternating matchings A_label,B_label. Choose one chord active: output 0 takes A at its opening and B at its closing. Passive chords take A at both ends. Output 1 takes the complements.

Every vertex has one horizontal and one vertical edge of each color. Cut before the active opening. Every passive chord lies wholly inside or outside the active chord; recursively cancel its nested identical involutions. The return permutations are exactly BA and AB. Each is a single cycle on either bipartition side because A∪B is Hamilton. Hence both outputs are Hamilton on the abstract layered vertex set. No commuting matchings or common label order are assumed.

Expand horizontal layer edges along their actual AAC intervals. A repeated physical AAC vertex appears in opposite interval parities, so its occurrences enter different outputs at every J coordinate. Marks occur once. Both expanded cycles are therefore simple. Every AAC edge has half its J copies in each output; every marked layer contributes half its J-cycle edges. Thus their common length is

    |V(J)|(E+q)/2,

where q is the AAC's number of marks. Per-label mark ownership partitions every J-direction edge, and the first anchored ownership already partitions all other edges.

The constructions below have q=bC/P. They give length

    |V(J)|(E+q)/2 = (P+L+b)·2^(n−r−1)=M_d.

A fork with two exclusive neighbors opens each cycle pair without changing length or ownership. There are mP AACs and 2mP paths.

## 5. Non-Mersenne odd parts: shift-stable source hierarchy

Assume either A≥4 or A=2,b≤L−3. Then r≥3. Choose k=r−2 and K=2^k=P/4. For r≥3, r≤2m·2^(r−2): at r=3 the bound holds even for m=1, and doubling the right side preserves it as r increases. Apply k standard squarings to each E_t, obtaining K sources of length R=2^(2mK), divisible by P. Put a=log₂A. This is the numerical choice used by the formalization.

Assign source branch j to code position j if j<a, and j+1 if j≥a, reserving bit a for a fresh profile twin. Source parent exponents satisfy 2m·2^j≥p(j)+1. Within a source torus use the positive profile: the first factor advances x at height x+y in S and y otherwise; the second takes the other positive edge. Use S={0} for A=2 and S={0,…,A/2−1}∪{A} otherwise. Its horizontal count is odd, so the N-step height-fiber translation is invertible and both factors are Hamilton. Their first A paths have common endpoints and are individually simple.

Profiles have physical SUM clocks modulo P. Apply h=r−k−1≥1 upper standard lifts. Within each source every final factor shares its full modulo P clock χ_source; source-prefix congruences persist under SUM and DIFFERENCE. Assign the profile bit a and remaining h positions to the paired upper configurations. There are P factors with all r-bit codes once.

The common-path lift prescribes each pair's literal endpoint phases c,c+A. For a required fixed-coordinate phase, each parent path forbids at most one connector candidate; three vertices in that phase fiber avoid both exclusions. The profile parent length R²≥P²≥3P supplies them. Thus arbitrary final codes are genuine geometric endpoints.

For every physical x and every δ modulo P, decoding gives exactly one factor with χ_source(x)=code+δ. Reverse profile bit 0 and retain profile bit 1 forward. Their mark classes are code−Au and code+Au respectively, u=0,…,b−1. The two shift owners for −Au and +Au have the same profile bit, because these shifts agree modulo 2A. Exactly one is eligible: the negative-shift owner if that bit is 0, the positive-shift owner if 1. Different u cannot duplicate one factor's mark. This proves exactly b marks per physical G vertex.

Use the balanced anti-L pattern

    turn_i=0 for 0≤i≤b;
    turn_i=(i−b) mod 2 for b<i<L;
    turn_(i+L)=1−turn_i.

Its agreement starts are 0,…,b−1 modulo L. The first seam has 1,0,0 as required. The common-pair flips preserve b-fold coverage.

Choose mark offset z=2 for A≥4, z=1 for A=2. Old anchor classes are code+z for reversed factors and code−z for forward factors modulo A. Fix all high code bits, including the profile bit, and vary all low a bits. Restricted decoding gives one old representative owner at each x. These are L groups of A factors, including source branches among the low bits.

For A≥4 each mark's neighbors at offsets 1 and 3 are unique unmarked degree-two vertices in opposite interval colors. This supplies the fork at the mark. For A=2,b≤L−3, turn_(b+1) is isolated in the common unflipped row h*: both adjacent intervals are unmarked, so the two nearest internal degree-two neighbors give the fork at that grid vertex. The pipeline in §4 yields the target paths in all these cases, including r=3, d=11 and d=13.

## 6. Mersenne odd parts: complementary unmarks and a corrected hierarchy

The remaining case is A=2, b=L−1, d=2P−1. For r≥4 choose k=r−2 and K=P/4. Then K≥4 and r+2≤2mK: the inequality holds at r=4,m=1 and is preserved as r increases. The K source cycles have length R divisible by D=4P. This again uses the maximal source depth, with one upper lift. Fresh A=2 profiles and h=r−k−1≥1 upper lifts give P factors; literal endpoint phases c,c+2 can be prescribed modulo D by the same connector avoidance.

Use the balanced period 2P turn word

    0^(P−1) 1^4 0 1^(P−4).

Its disagreement starts are B₀={P−2,P+2,P+3,2P−1}. In a reverse profile twin, unmarked offsets relative to its own code are −2B₀; in the forward twin they are +2B₀.

There are r free code positions in 0,…,r+1; bits 2,3 are fixed zero. Code bit 0 is source branch b₀, bit 1 the profile twin ε, bit 4 is b₁ when m≥2 and b₁(1−b₀) when m=1. Source branch j≥2 occupies bit j+3; upper configurations occupy the remaining high positions. A pair has codes c,c+2 without carry. Numerical codes can repeat across distinct sources in the exceptional m=1 odd branch; this is intentional.

Every source clock has common physical parity. Within fixed b₀ all suffix clocks agree modulo 16. At branch j≥2 clocks agree through bit j+3 because 2m·2^j≥j+4. At branch 1 they agree modulo 32 when m≥2. When m=1 they satisfy χ_(b₁1)=17χ_(b₁0) modulo 32, a difference 16 times physical parity. Profile SUM and upper DIFFERENCE preserve these identities.

Fix a physical G vertex. Its clock parity uniquely chooses b₀. The eight combinations of ε and its four disagreement offsets, including the code's +2ε, exhaust all even residues modulo 16 exactly once. The common low-16 clock therefore chooses exactly one ε and one full offset δ modulo D. Subtract this full δ before further decoding, retaining every carry.

For b₀ even or m≥2, ordinary bit 4 decoding chooses b₁. For m=1,b₀ odd, both code bit 4 values are zero, but the two clocks differ by 16, so exactly one has the required bit 4 after subtraction. Later source bits are uniquely selected by their common-prefix clocks; remaining upper bits complete χ−δ. Thus exactly one factor is UNMARKED at every physical G vertex.

Old spacing-two groups fix all addresses except b₀ and pair its two choices. Codes have opposite parity, so their old representatives partition V(G), independently of the exceptional bit 4 change. There are L groups; each physical vertex lies in L interiors. Removing the unique unmarked appearance leaves L−1 marks. Reciprocal profile-pair flips preserve this coverage. The turn word's isolated zero at P+3 in the unflipped h* row gives the exclusive-neighbor fork. The pipeline yields length (2P−1)·2^(n−r−1).

For r=3, d=15, use the separately proved four-source construction: its modulo 32 sibling correction is the same scalar 17 when m=1; phase starts 0,16,1,1 (m=1) or 0,16,1,17 (m≥2) partition unmarked classes. There are zero upper lifts, so use explicit shifted single-height profiles S={c}; the common two-edge paths (0,c)→(1,c+1) have phases c,c+2. This supplies genuine endpoints without assuming arbitrary phase prescription. The old parity pairs, long pattern, labeling and fork then apply. For r=2, d=7, square each E_t once to obtain two source cycles with common modulo 4 clock. On their squares use positive profiles S={0} and S={1}. Their literal two-step endpoints have phases 0,2 and 1,3; all four profile cycles share the same SUM clock modulo 4. Reverse the first owner of each pair and keep its partner forward. Source 0 old anchors are odd; source 1 old anchors are even. Cross-source pairing supplies two old groups for H=Q_(4m); the four new quarter mark classes partition G=Q_(8m). Use turn 0011 and the common h* merge chain. Reciprocal endpoint exchanges preserve the mark partition. In any flipped row, column 1 has neighboring turns 1,0,1, so both incident vertical intervals are unmarked and give exclusive A=2 interior neighbors. Fold with E_t on J=Q_(2m) and open the fork, giving 8m paths of length 7·2^(14m−3). This explicit shifted-profile boundary needs no arbitrary zero-lift phase prescription. For r=1, d=3, §3 applies.

## 7. Exhaustion and conclusion

Odd part d=1 is covered by Hamilton cutting. Every two-bit odd part is P+1 and is covered by §3. Every odd part with at least three ones is uniquely P+L+b. Non-Mersenne cases fall in §5, including their minimal r=3 boundary. Mersenne cases fall in §6, including d=7 and d=15. No admissible odd divisor is omitted. Each maximal length M_d therefore has a simple path decomposition, and §1 cuts it into the requested ℓ-edge paths.

`OddFrontiers.frontiers` implements this exhaustive branch assembly. `Conjecture.erde_even_hypercube` applies `Parameters.target_from_odd_frontiers` to the actual proved frontiers. `Conjecture.paths` exposes the exact quantified hypotheses and the simple-path edge-partition conclusion. The theorem has no surviving factor, mark-count, schedule, geometry, frontier-existence or coverage hypothesis.

## Formal proof map

All paths below are relative to this repository. Importing [Conjecture.lean](ErdePaths/Conjecture.lean) imports the complete dependency closure. The mathematical construction is uniform in m and in the binary complexity of the positive odd remainder b.

| Part of the argument | Lean sources and public entry points |
|---|---|
| Exact graph and path statement | [Basic](ErdePaths/Basic.lean): `Adjacent`, `IsSimplePath`, `HasPathDecomposition`; [Binary](ErdePaths/Binary.lean): binary-tuple bijection and adjacency; [GraphTarget](ErdePaths/GraphTarget.lean): `GraphTarget.to_target` |
| Arithmetic reduction and subdivision (§1) | [Parameters](ErdePaths/Parameters.lean): `normalize`, `frontier_divides`, `target_from_odd_frontiers`; [Subdivision](ErdePaths/Subdivision.lean): `subdivision` |
| Actual even-cube Hamilton factors | [EvenHamilton](ErdePaths/EvenHamilton.lean): `decomposition`; [HamiltonSquare](ErdePaths/HamiltonSquare.lean), [HamiltonTower](ErdePaths/HamiltonTower.lean) |
| Actual square clocks and causal ownership (§2) | [SquareLift](ErdePaths/SquareLift.lean), [HierarchicalDecode](ErdePaths/HierarchicalDecode.lean), [SourceProfile](ErdePaths/SourceProfile.lean), [SourceStability](ErdePaths/SourceStability.lean), [SourceAnchorGroups](ErdePaths/SourceAnchorGroups.lean) |
| Two-bit frontiers (§3) | [TwoBitFrontier](ErdePaths/TwoBitFrontier.lean): `frontier`; [AnchoredAssembly](ErdePaths/AnchoredAssembly.lean), [SubdividedWiggle](ErdePaths/SubdividedWiggle.lean), [ForkWiggle](ErdePaths/ForkWiggle.lean) |
| Actual AAC traversal and marks (§4) | [AACTransition](ErdePaths/AACTransition.lean), [AACMerge](ErdePaths/AACMerge.lean), [AACFineClock](ErdePaths/AACFineClock.lean), [AACMarkWord](ErdePaths/AACMarkWord.lean), [AACPatternCardinality](ErdePaths/AACPatternCardinality.lean) |
| Reciprocal endpoint exchange (§4) | [ReciprocalEndpoints](ErdePaths/ReciprocalEndpoints.lean), [AACMarkExchange](ErdePaths/AACMarkExchange.lean), [SourceMarkMulticover](ErdePaths/SourceMarkMulticover.lean) |
| Balanced marks, Hall labels and noncrossing return (§4) | [AACPhysicalBalance](ErdePaths/AACPhysicalBalance.lean), [NoncrossingMatch](ErdePaths/NoncrossingMatch.lean), [HallMarriage](ErdePaths/HallMarriage.lean), [HallColor](ErdePaths/HallColor.lean), [MarkSchedule](ErdePaths/MarkSchedule.lean), [LayerPartition](ErdePaths/LayerPartition.lean) |
| Simple folded tours and exact local/global edge ownership (§4) | [AACFoldClock](ErdePaths/AACFoldClock.lean), [AACFoldEdgeLedger](ErdePaths/AACFoldEdgeLedger.lean), [SourceLocalFold](ErdePaths/SourceLocalFold.lean), [SourceMarkedProduct](ErdePaths/SourceMarkedProduct.lean), [CubePairedPartition](ErdePaths/CubePairedPartition.lean) |
| Ordinary buffered frontiers (§5) | [SourceUniformInput](ErdePaths/SourceUniformInput.lean): `input`; [SourceGlobalPaths](ErdePaths/SourceGlobalPaths.lean): `Input.cube`; [SourceUniformPaths](ErdePaths/SourceUniformPaths.lean): `frontier` |
| Ordinary isolated frontiers (§5) | [AACIsolatedOpening](ErdePaths/AACIsolatedOpening.lean), [SourceIsolatedPaths](ErdePaths/SourceIsolatedPaths.lean), [SourceIsolatedFrontier](ErdePaths/SourceIsolatedFrontier.lean): `frontier` |
| Complementary frontiers (§6) | [MersenneCodeOrigins](ErdePaths/MersenneCodeOrigins.lean), [MersenneReciprocalMulticover](ErdePaths/MersenneReciprocalMulticover.lean), [MersenneUniformInput](ErdePaths/MersenneUniformInput.lean), [MersenneUniformPaths](ErdePaths/MersenneUniformPaths.lean): `frontier` |
| Forced zero-depth boundaries (§6) | [ZeroUpperCodeOrigins](ErdePaths/ZeroUpperCodeOrigins.lean), [ZeroUpperIncidence](ErdePaths/ZeroUpperIncidence.lean), [QuarterProfileOrigins](ErdePaths/QuarterProfileOrigins.lean), [QuarterReciprocalMulticover](ErdePaths/QuarterReciprocalMulticover.lean), [SevenFrontier](ErdePaths/SevenFrontier.lean): `frontier`; [FifteenFrontier](ErdePaths/FifteenFrontier.lean): `frontier` |
| Every odd coefficient and the full theorem (§7) | [PowerFrontier](ErdePaths/PowerFrontier.lean), [OddClassification](ErdePaths/OddClassification.lean), [OddFrontiers](ErdePaths/OddFrontiers.lean): `frontiers`; [Conjecture](ErdePaths/Conjecture.lean): `erde_even_hypercube`, `paths` |

The public frontier theorems construct genuine factors, profiles, marks, schedules, local openings and full cube edge ownership internally. The conditional arithmetic theorem `target_from_odd_frontiers` is supplied with the unconditional proved `OddFrontiers.frontiers`; its premise does not survive in the final theorem.

## Literature

- Joshua Erde, [*Decomposing the cube into paths*, arXiv:1310.6776v1](https://arxiv.org/abs/1310.6776v1), 2013. The target is Conjecture 8 in §3; Lemma 6 states the even-cube Hamilton input.
- Maria Axenovich, David Offner and Casey Tompkins, [*Long path and cycle decompositions of even hypercubes*, arXiv:1905.10114](https://arxiv.org/abs/1905.10114), [European Journal of Combinatorics version](https://doi.org/10.1016/j.ejc.2021.103320). This gives earlier general ranges for even cubes; those range theorems are not assumptions of this formalization.

The references identify the original question and relevant prior work. This release does not claim that its construction is novel or that the literature review establishes priority.
