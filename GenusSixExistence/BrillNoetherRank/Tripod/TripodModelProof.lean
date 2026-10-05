import GenusSixExistence.BrillNoetherRank.Tripod.TripodModelDefs
import Utilities.Subdivision.ScaleLift
import GenusSixExistence.BrillNoetherRank.Tripod.TripodMarkRefinement
import DraismaVargas.LocalCases.StableModelPackaging
import Utilities.Gonality.CoreBridgeless
import Utilities.Subdivision.OddSubdivisionDescent

/-!
# Every bridgeless genus-six graph with three marks has a tripod model

Prose proof: `Research/genus-six-brill-noether-rank.md`, §6.2 (The tripod model); section numbers
in this file refer to that note. The model is an expansion of the marked core onto the reduced
presentation of `G`, split at its bivalent marks, with Laplacian equivalences to the
subdivisions of `G` at every scale (§8.3). The structure `Closure.TripodModel` is in `TripodModelDefs.lean`; `Closure.exists_tripodModel`
calls `exists_tripodModel` below.

## The construction

1. **The reduced model** (`exists_reducedModel`). The reduction to a marked specification is re-run so that its
   Laplacian equivalence is kept:
   `DraismaVargas.LocalCases.StableModelPackaging.exists_markedSpec_of_bridgeless` gives the
   reduced specification `spec₀` of `G` (bivalent vertices suppressed except loop markers, the
   input being already bridgeless) and a Laplacian equivalence `spec₀.graph ≃ G`;
   `StableModelReduction.exists_markerExpansion` gives the cubic expansion `D₀`, with
   `2 (g - 1) = 10` vertices and `3 (g - 1) = 15` slots at genus six.
2. **Mark placement** (`MarkRefinement.exists_markStep`, three times). Each mark is pulled back to
   a vertex of the current small graph, and the big core is subdivided at it: a zero mark piece at
   a vertex of valence at least three, a split `double` at a loop marker, and a split of the small
   slot (and of its owner) at a bivalent vertex. Repeated marks fall under the same rules, the
   later mark being placed against the earlier mark vertex, so they are joined by zero pieces.
3. **The transport at every scale** (`Utilities.Subdivision.ScaleLift.exists_scaledEquiv`). The composite Laplacian
   equivalence `small.graph ≃ G` at scale one sends the three small mark vertices to the chips of
   `E`; its lift to every scale `u` commutes with `fineOf`, hence with `embed`.
4. **The legs**: `4 L + 1`, where `L` is the total degenerate length.
-/

namespace GenusSixExistence.Tripod.TripodModelProof

open DraismaVargas.Count
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion (ExpansionData)
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open Gadget Closure Utilities.Subdivision.ScaleLift MarkRefinement

/-! ## 1.  Small facts -/

/-- An effective divisor of degree three is a sum of three chips. -/
theorem exists_three_chips {G : CFGraph} (E : CFDiv G) (hE : effective E) (hdeg : deg E = 3) :
    ∃ y : Fin 3 → G.V, E = ∑ k, one_chip (y k) := by
  obtain ⟨A, B, hA, hB, hAdeg, hBdeg, hsplit⟩ :=
    effective_divisor_decomposition G E 2 1 hE (by rw [hdeg]; norm_num)
  obtain ⟨x₁, x₂, hx⟩ := exists_chip_pair_of_effective_deg_two G A hA (by rw [hAdeg]; norm_num)
  obtain ⟨x₃, h3⟩ := effective_degree_one_eq_one_chip B hB (by rw [hBdeg]; norm_num)
  refine ⟨![x₁, x₂, x₃], ?_⟩
  rw [Fin.sum_univ_three, hsplit, hx, h3]
  simp

/-- The bridgelessness of `Utilities.Subdivision.CoreCutsAndFlats` (no slot disconnects the
core) gives that of `SpecBridge` (no slot is the only one crossing a cut), on a connected core. -/
theorem specBridgeless_of_bridgeless {n p : ℕ} {C : Core n p} (hC : C.Connected)
    (hb : C.Bridgeless) : DraismaVargas.LocalCases.SpecBridge.Bridgeless C := by
  rintro e ⟨left, hv⟩
  apply hb e
  refine ⟨Finset.notMem_empty e, (C.connectedOff_empty_iff).mpr hC, ?_⟩
  intro hcon
  obtain ⟨f, hf, hcross⟩ := hcon left ⟨C.tail e, C.head e, hv.1, hv.2.1⟩
  have hfe : f ≠ e := by simpa using hf
  have hiff := hv.2.2 f hfe
  unfold ExplicitPotential.Core.Crosses at hcross
  tauto

/-- A cubic core has an incident slot at every vertex. -/
theorem incident_of_cubic {n p : ℕ} {C : Core n p} (h : C.Cubic) (v : Fin n) :
    ∃ i, C.tail i = v ∨ C.head i = v := by
  by_contra hno
  push Not at hno
  have h3 := h v
  unfold ExplicitPotential.Core.incidenceDegree at h3
  rw [Finset.sum_eq_zero (fun i _ ↦ by simp [(hno i).1, (hno i).2])] at h3
  omega

theorem mapDiv_sum_one_chip {G H : CFGraph} (Φ : LaplacianEquiv G H) (y : Fin 3 → G.V) :
    Φ.mapDiv (∑ k, one_chip (y k)) = ∑ k, one_chip (Φ (y k)) := by
  funext z
  simp only [LaplacianEquiv.mapDiv_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← LaplacianEquiv.mapDiv_one_chip]
  rfl

/-! ## 2.  The reduced model -/

/-- **The reduced model of a bridgeless genus-six graph, with its Laplacian equivalence**:
`exists_expansionModel` re-run on a bridgeless input so that the equivalence of the reduced
specification with `G` is kept. -/
theorem exists_reducedModel (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G = 6)
    (hb : (UnitSubdivisionPresentation.spec G).core.Bridgeless) :
    ∃ (n₀ p₀ N Q : ℕ) (spec₀ : Spec n₀ p₀) (D₀ : ExpansionData n₀ p₀ N Q),
      N = 10 ∧ Q = 15 ∧ D₀.Conditions spec₀.core ∧ D₀.bigCore.Cubic ∧ D₀.bigCore.Connected ∧
        Nonempty (LaplacianEquiv spec₀.graph (UnitSubdivisionPresentation.spec G).graph) := by
  have hE := card_edges_sub_card_vertices' G hg
  have hconn := Utilities.Gonality.coreConnected_unitSpec G hG
  obtain ⟨n₀, p₀, spec₀, mk, hbase, hc₀, hb₀, hlt₀, hg₀, hφ, -⟩ :=
    DraismaVargas.LocalCases.StableModelPackaging.exists_markedSpec_of_bridgeless (UnitSubdivisionPresentation.spec G)
      hconn (specBridgeless_of_bridgeless hconn hb) (by omega)
  have hstable : DraismaVargas.LocalCases.StableModelReduction.Stable mk :=
    DraismaVargas.LocalCases.BridgeReduction.stable_of_bridgeless mk spec₀.core_loopless hbase hb₀
  obtain ⟨D₀, hCond, hCubic, hConnBig⟩ :=
    DraismaVargas.LocalCases.StableModelReduction.exists_markerExpansion mk hstable spec₀.core_loopless hc₀
  exact ⟨n₀, p₀, _, _, spec₀, D₀, by omega, by omega, hCond, hCubic, hConnBig, hφ⟩
where
  card_edges_sub_card_vertices' (H : CFGraph.{0}) (hgenus : genus H = 6) :
      (Multiset.card H.edges : ℤ) - Fintype.card H.V = 5 := by
    have hgen : (Multiset.card H.edges : ℤ) - Fintype.card H.V + 1 = 6 := hgenus
    omega

/-! ## 3.  The marks, the transport and the legs -/

/-- **The tripod model built from a reduced model** (§6.2). -/
theorem tripodModel_of_reduced (G : CFGraph.{0})
    (E : CFDiv (UnitSubdivisionPresentation.spec G).graph) {n₀ p₀ N Q : ℕ} (spec₀ : Spec n₀ p₀)
    (D₀ : ExpansionData n₀ p₀ N Q) (hN : N = 10) (hQ : Q = 15)
    (hCond : D₀.Conditions spec₀.core) (hCubic : D₀.bigCore.Cubic)
    (hConnBig : D₀.bigCore.Connected)
    (φ : LaplacianEquiv spec₀.graph (UnitSubdivisionPresentation.spec G).graph)
    (y : Fin 3 → (UnitSubdivisionPresentation.spec G).graph.V)
    (hy : E = ∑ k, one_chip (y k)) : Nonempty (TripodModel G E) := by
  subst hN hQ
  -- the three marks, one at a time
  obtain ⟨n₁, p₁, s₁, D₁, e₁, ι₁, w₁, χ₁, hC₁, hB₁, hI₁, hf₁, -, hχ₁, -⟩ :=
    exists_markStep spec₀ D₀ hCond (incident_of_cubic hCubic) (φ.toEquiv.symm (y 0))
  obtain ⟨n₂, p₂, s₂, D₂, e₂, ι₂, w₂, χ₂, hC₂, hB₂, hI₂, hf₂, hfc₂, hχ₂, hχι₂⟩ :=
    exists_markStep s₁ D₁ hC₁ hI₁ ((χ₁.trans φ).toEquiv.symm (y 1))
  obtain ⟨n₃, p₃, s₃, D₃, e₃, ι₃, w₃, χ₃, hC₃, hB₃, -, hf₃, hfc₃, hχ₃, hχι₃⟩ :=
    exists_markStep s₂ D₂ hC₂ hI₂ ((χ₂.trans (χ₁.trans φ)).toEquiv.symm (y 2))
  -- the composite equivalence at scale one, and where it sends the marks
  set Φ := χ₃.trans (χ₂.trans (χ₁.trans φ)) with hΦdef
  set mk : Fin 3 → Fin n₃ := ![ι₃ (ι₂ w₁), ι₃ w₂, w₃] with hmk
  have hΦ : ∀ k, Φ (s₃.coreVertex (mk k)) = y k := by
    intro k
    fin_cases k
    · show φ (χ₁ (χ₂ (χ₃ (s₃.coreVertex (ι₃ (ι₂ w₁)))))) = y 0
      rw [hχι₃, hχι₂, hχ₁]
      exact φ.toEquiv.apply_symm_apply _
    · show (χ₁.trans φ) (χ₂ (χ₃ (s₃.coreVertex (ι₃ w₂)))) = y 1
      rw [hχι₃, hχ₂]
      exact (χ₁.trans φ).toEquiv.apply_symm_apply _
    · show (χ₂.trans (χ₁.trans φ)) (χ₃ (s₃.coreVertex w₃)) = y 2
      rw [hχ₃]
      exact (χ₂.trans (χ₁.trans φ)).toEquiv.apply_symm_apply _
  have hfib : ∀ k, D₃.fib (markVertex 10 k) = mk k := by
    intro k
    fin_cases k
    · show D₃.fib (Fin.last 10).castSucc.castSucc = _
      rw [hfc₃, hfc₂, hf₁]
      rfl
    · show D₃.fib (Fin.last (10 + 1)).castSucc = _
      rw [hfc₃, hf₂]
      rfl
    · show D₃.fib (Fin.last (10 + 1 + 1)) = _
      rw [hf₃]
      rfl
  refine ⟨{
    core := D₀.bigCore
    cubic := hCubic
    connected := hConnBig
    loopless := ExpansionData.loopless_of_conditions hCond
    slots := ⟨e₁, e₂, e₃⟩
    smallVertices := n₃
    smallSlots := p₃
    small := s₃
    smallMark := mk
    expansion := D₃
    bigCore_eq := by rw [hB₃, hB₂, hB₁]; rfl
    conditions := hC₃
    fib_mark := hfib
    transport := ?_
    legs := fun _ ↦ 4 * (∑ i, degenerateLength D₃ s₃ i) + 1
    long := fun _ ↦ Nat.lt_succ_self _ }⟩
  intro u hu
  obtain ⟨ψ, hψ⟩ := exists_scaledEquiv Φ u hu
  refine ⟨ψ, ?_⟩
  rw [mapDiv_embed Φ u hu ψ hψ, hy, mapDiv_sum_one_chip]
  simp only [hΦ]

/-! ## 4.  The theorem -/

/-- **Tripod models exist** (§6.2). Every connected
bridgeless graph of genus six, with every effective divisor of degree three on its vertices, has
a tripod model. -/
theorem exists_tripodModel (G : CFGraph.{0}) (hG : graph_connected G) (hg : genus G = 6)
    (hb : (UnitSubdivisionPresentation.spec G).core.Bridgeless)
    (E : CFDiv (UnitSubdivisionPresentation.spec G).graph) (hE : effective E) (hdeg : deg E = 3) :
    Nonempty (TripodModel G E) := by
  obtain ⟨n₀, p₀, N, Q, spec₀, D₀, hN, hQ, hCond, hCubic, hConnBig, ⟨φ⟩⟩ :=
    exists_reducedModel G hG hg hb
  obtain ⟨y, hy⟩ := exists_three_chips E hE hdeg
  exact tripodModel_of_reduced G E spec₀ D₀ hN hQ hCond hCubic hConnBig φ y hy

end GenusSixExistence.Tripod.TripodModelProof
