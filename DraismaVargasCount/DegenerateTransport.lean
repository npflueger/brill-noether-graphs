module

public import DraismaVargasCount.DegenerateFibreCover
public import Utilities.Harmonic.Basic

@[expose] public section

/-!
# Rank at the degenerate request, transport half: a counting refutation of the covering half, and the shape that survives

The rank statement `DegenerateBigDivisor.ForestContractionRank` is a step of the
endgame (step 5 of `Assembly`).  `DegenerateFibreCover` splits
`Utilities.Certificate.GraphContractionCertificate.PushableReachabilityAtRepresentatives`
for `bigDivisor` into **(T)** `FibreTransportFrom` (metric-fibre transport by a
script pulled back from the small side) and **(C)** `FibreCover` (every vertex
of the small subdivision already carries a chip of *some* member of the
member's pencil of fibre divisors), and proves that (T) and (C) together give
`DegenerateBigDivisor.ForestContractionRank`.

This file opens the transport half.  Its main result is negative and is about
the *other* half.

## 1.  The count that kills (C)

The pencil is indexed by `member.target.V`, and the target is the member's own
target tree: a **fixed** finite graph, whose size is pinned by
`FullDimensionalSourcePresentation.saturated` and does not grow with the scale
`k`.  Each member of the pencil pushes forward to an *effective* divisor of
degree `degree` on `(small.scale k hk).graph`, so its support has at most
`degree` vertices.  Hence

    FibreCover  →  Fintype.card (small.scale k hk).Vertex
                     ≤ Fintype.card member.target.V * degree,

and the left-hand side is `n + ∑ e, (k * small.length e - 1)`, which is strictly
increasing and unbounded in `k`.  `card_target_vertex_eq` turns the right-hand
side into the `k`-free quantity `(2 * genus member.data.sourceGraph +
2 * degree - 4) * degree`.  So **(C) is false for every large enough scale**,
and `not_fibreCover_of_card_lt`, `not_fibreCover_of_large_scale` and
`not_fibreCover_of_scale_large` say so at three levels of explicitness.

The same count refutes (C)'s stated reduction
`DegenerateFibreCover.RealizationSurjective` — by a shorter route, since a
surjection out of `member.data.SourceVertex` cannot reach more than
`Fintype.card member.target.V * degree` vertices — and it refutes surjectivity
of the placement `DegeneratePlacement.sourcePoint` itself.

## 2.  What the count does *not* touch

`PushableReachabilityAtRepresentatives` asks for a chip that can be **moved** to
the contraction fibre over `b`, by a script chosen separately for each `b`.  The
count above applies only to the strengthening in which finitely many *static*
divisors must already carry the chip.  `TransportedCover` below is exactly the
hypothesis `DegenerateFibreCover.pushableReachabilityAtRepresentatives_of_transportedCover`
consumes, with (T) and (C) fused; `transportedCover_of_transport_cover` shows
(T) and (C) imply it, and `forestContractionRank_of_transportedCover` shows it
suffices.  Nothing here refutes `TransportedCover`, and nothing here is evidence
against `ForestContractionRank`: `PushableReachabilityAtRepresentatives` is a *sufficient*
condition for rank one, as `DegenerateFibreCover`'s own header records.

## 3.  The natural route to (T), and why it dies the same way

(T) demands `bigDivisor … root' = bigDivisor … root + prin … (c.pullScript tau)`.
The obvious route is to move the divisor upstairs, on the member's own source
graph, where the pencil is the literal pullback of a point of a tree, and then
push forward along the placement.  `fibreTransportFrom_of_placementTransport`
is that route, stated exactly: it needs the placement to be a **valid**
contraction certificate (`placementCertificate`), because
`GraphContractionCertificate.pushDiv_prin_pullScript` is the only thing that
turns a pushed-forward principal divisor back into a principal one.  And
`not_placementCertificate_valid_of_card_lt` shows that hypothesis is false at
large scale, by the §1 count again: validity includes surjectivity of the
placement.

## 4.  The shape that survives

`forestContractionRank_of_harmonicFibre` reduces `ForestContractionRank` to a
single geometric obligation on the **small** side: a harmonic morphism from the
small subdivision to a connected genus-zero graph whose fibre is the
pushforward of `bigDivisor`.  This is `DegenerateBigDivisor`'s own reading of
the rank statement — "the member's fibre is a `g^1_4` on the metric graph the member
realizes" — and it uses only the public harmonic-morphism machinery
`IndexedHarmonicData` of `Utilities.Harmonic.Basic`.  The target there is a *subdivision of*
`member.target`, not `member.target` itself: `IndexedHarmonicData` forbids
contracted edges, so at scale `k` the tree has to be subdivided to match.

## What is NOT proved

* **`ForestContractionRank` is not proved**, and nothing here is evidence
  against it.  What is proved false, at large scale, is the (C) half of one
  particular *sufficient* split of it.
* **(T) `FibreTransportFrom` is neither proved nor refuted.**  The count of §1
  does not apply to it: it is an equality between two members of the pencil, not
  a covering claim.  Only the *route* to it through a valid placement
  certificate is refuted, and only at large scale.
* `TransportedCover` is not proved.
* `forestContractionRank_of_harmonicFibre` takes the harmonic datum, its
  `PullbackPrincipalCompatible` receipt, the target's connectedness and
  genus-zero receipts, and the identification of its fibre with the pushforward
  **all as hypotheses**.  No such datum is constructed here.
* The refutations are conditional on an explicit numeric inequality; no lower
  bound on `k` is asserted for any particular application.

No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`.
-/

namespace DraismaVargas.Count.DegenerateTransport

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.Count.DegenerateBigDivisor
open DraismaVargas.Count.DegenerateFibreCover
open RowRealizedPosition SlotMoment
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

/-! ## 1.  Three counting facts, none of them about subdivisions -/

section Counting

variable {G : CFGraph}

/-- **An effective divisor has a small support.**  At most `deg` vertices carry
a chip. -/
theorem card_support_le_deg {E : CFDiv G} (hEff : effective E) :
    ((Finset.univ.filter fun v : G.V ↦ 0 < E v).card : ℤ) ≤ deg E := by
  classical
  have hcard : ((Finset.univ.filter fun v : G.V ↦ 0 < E v).card : ℤ) =
      ∑ _v ∈ Finset.univ.filter (fun v : G.V ↦ 0 < E v), (1 : ℤ) := by simp
  have hstep : ∑ _v ∈ Finset.univ.filter (fun v : G.V ↦ 0 < E v), (1 : ℤ) ≤
      ∑ v ∈ Finset.univ.filter (fun v : G.V ↦ 0 < E v), E v := by
    refine Finset.sum_le_sum fun v hv ↦ ?_
    have := (Finset.mem_filter.mp hv).2
    omega
  have hrest : ∑ v ∈ Finset.univ.filter (fun v : G.V ↦ 0 < E v), E v ≤ ∑ v : G.V, E v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ ↦ hEff v
  rw [hcard]
  exact le_trans hstep hrest

/-- The natural-number form, for a divisor of known natural degree. -/
theorem card_support_le_of_deg {E : CFDiv G} (hEff : effective E) {d : ℕ}
    (hDeg : deg E = (d : ℤ)) :
    (Finset.univ.filter fun v : G.V ↦ 0 < E v).card ≤ d := by
  have h := card_support_le_deg hEff
  rw [hDeg] at h
  exact_mod_cast h

end Counting

/-- **A finite type covered by few small sets is small.** -/
theorem card_le_of_cover {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (S : β → Finset α) (d : ℕ) (hS : ∀ b : β, (S b).card ≤ d)
    (hCover : ∀ a : α, ∃ b : β, a ∈ S b) :
    Fintype.card α ≤ Fintype.card β * d := by
  classical
  have hsub : (Finset.univ : Finset α) ⊆ Finset.univ.biUnion S := by
    intro a _
    obtain ⟨b, hb⟩ := hCover a
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hb⟩
  calc Fintype.card α = (Finset.univ : Finset α).card := rfl
    _ ≤ (Finset.univ.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ b : β, (S b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b : β, d := Finset.sum_le_sum fun b _ ↦ hS b
    _ = Fintype.card β * d := by simp [Finset.sum_const, Finset.card_univ]

/-- The vertex count of a subdivision specification. -/
theorem card_vertex {n p : ℕ} (spec : Spec n p) :
    Fintype.card spec.Vertex = n + ∑ e : Fin p, (spec.length e - 1) := by
  simp [Spec.Vertex, Spec.Interior]

/-- **The source graph of a gluing datum is small.**  A source vertex is a pair
(target vertex, sheet block), so there are at most `card target.V * degree` of
them — independently of any scale. -/
theorem card_sourceVertex_le {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) :
    Fintype.card data.SourceVertex ≤ Fintype.card target.V * degree := by
  classical
  have h : Fintype.card data.SourceVertex ≤ Fintype.card (target.V × Fin degree) :=
    Fintype.card_le_of_injective (fun x ↦ x.1) Subtype.val_injective
  simpa using h

/-- **The member's target tree has a scale-free vertex count.**  It is connected
of genus zero, so `|V| = |E| + 1`, and `saturated` pins `|E|`.  Nothing on the
right depends on the requested lengths, hence nothing depends on the scale. -/
theorem card_target_vertex_eq {n p degree : ℕ}
    {core : Utilities.Certificate.ExplicitPotential.Core n p} {y : Fin p → ℚ}
    (member : FibreMember core y degree) :
    (Fintype.card member.target.V : ℤ) =
      2 * genus member.data.sourceGraph + 2 * (degree : ℤ) - 4 := by
  have hGenus : genus member.target = 0 := member.fullDim.targetGenus
  have hSat : (Multiset.card member.target.edges : ℤ) =
      2 * genus member.data.sourceGraph + 2 * (degree : ℤ) - 5 := member.fullDim.saturated
  unfold genus at hGenus
  omega


/-! ## 2.  The degenerate pencil, and the count that refutes (C) -/

section Obligations

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

/-- The pushforward of a member of the pencil is effective. -/
theorem effective_pushDivisor_bigDivisor (root : member.target.V) :
    effective (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
      (bigDivisor D small hN hL k hk member hClosed hScale root)) := by
  rw [pushDivisor_eq_pushDiv D (small.scale k hk) hN hL]
  exact (ExpansionData.certificate D (small.scale k hk) hN hL).effective_pushDiv
    (bigDivisor_effective D small hN hL k hk member hClosed hScale root)

/-- The pushforward of a member of the pencil has the member's degree. -/
theorem deg_pushDivisor_bigDivisor (root : member.target.V) :
    deg (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
      (bigDivisor D small hN hL k hk member hClosed hScale root)) = (degree : ℤ) := by
  rw [pushDivisor_eq_pushDiv D (small.scale k hk) hN hL,
    GraphContractionCertificate.deg_pushDiv]
  exact bigDivisor_degree D small hN hL k hk member hClosed hScale root

/-- **(C) forces a vertex count.**  The pencil has one member per vertex of the
member's target tree; each pushes forward to an effective divisor of degree
`degree`, hence with at most `degree` vertices in its support.  Their supports
therefore cover at most `card member.target.V * degree` vertices, and (C) says
they cover all of them. -/
theorem card_vertex_le_of_fibreCover
    (hCover : FibreCover D small hN hL k hk member hClosed hScale) :
    Fintype.card (small.scale k hk).Vertex ≤
      Fintype.card member.target.V * degree := by
  classical
  refine card_le_of_cover
    (fun root : member.target.V ↦
      Finset.univ.filter fun b : (small.scale k hk).Vertex ↦
        0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
          (bigDivisor D small hN hL k hk member hClosed hScale root) b)
    degree (fun root ↦ ?_) (fun b ↦ ?_)
  · exact card_support_le_of_deg
      (effective_pushDivisor_bigDivisor D small hN hL k hk member hClosed hScale root)
      (deg_pushDivisor_bigDivisor D small hN hL k hk member hClosed hScale root)
  · obtain ⟨root, hPos⟩ := hCover b
    exact ⟨root, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hPos⟩⟩

/-- **The surjectivity form of (C) forces the same count**, by a shorter route:
the small subdivision would be a surjective image of the member's source graph,
which has at most `card member.target.V * degree` vertices. -/
theorem card_vertex_le_of_realizationSurjective
    (hSurj : RealizationSurjective D small hN hL k hk member hClosed hScale) :
    Fintype.card (small.scale k hk).Vertex ≤
      Fintype.card member.target.V * degree :=
  le_trans (Fintype.card_le_of_surjective _ hSurj) (card_sourceVertex_le member.data)

/-- **(C) is false once the small subdivision has too many vertices.** -/
theorem not_fibreCover_of_card_lt
    (hlt : Fintype.card member.target.V * degree <
      n + ∑ e : Fin p, (k * small.length e - 1)) :
    ¬ FibreCover D small hN hL k hk member hClosed hScale := by
  intro hCover
  have h := card_vertex_le_of_fibreCover D small hN hL k hk member hClosed hScale hCover
  rw [card_vertex] at h
  simp only [Spec.scale_length] at h
  omega

/-- **The surjectivity form of (C) is false under the same inequality.** -/
theorem not_realizationSurjective_of_card_lt
    (hlt : Fintype.card member.target.V * degree <
      n + ∑ e : Fin p, (k * small.length e - 1)) :
    ¬ RealizationSurjective D small hN hL k hk member hClosed hScale := by
  intro hSurj
  have h := card_vertex_le_of_realizationSurjective D small hN hL k hk member hClosed
    hScale hSurj
  rw [card_vertex] at h
  simp only [Spec.scale_length] at h
  omega

/-- The same, read off a single slot: one slot of the small core already makes
the subdivision grow linearly in the scale. -/
theorem not_fibreCover_of_large_scale (e₀ : Fin p)
    (hlt : Fintype.card member.target.V * degree + 1 < n + k * small.length e₀) :
    ¬ FibreCover D small hN hL k hk member hClosed hScale := by
  refine not_fibreCover_of_card_lt D small hN hL k hk member hClosed hScale ?_
  have hmem : k * small.length e₀ - 1 ≤ ∑ e : Fin p, (k * small.length e - 1) :=
    Finset.single_le_sum (f := fun e : Fin p ↦ k * small.length e - 1)
      (fun e _ ↦ Nat.zero_le _) (Finset.mem_univ e₀)
  have hpos : 0 < k * small.length e₀ := Nat.mul_pos hk (small.length_pos e₀)
  omega

/-- **(C) is false at large scale, with a scale-free right-hand side.**  Only
`genus member.data.sourceGraph` and `degree` enter the bound; both are fixed by
the big core and the pencil degree, so the inequality holds for all large `k`. -/
theorem not_fibreCover_of_scale_large (e₀ : Fin p)
    (hlt : (2 * genus member.data.sourceGraph + 2 * (degree : ℤ) - 4) * (degree : ℤ) + 1 <
      (n : ℤ) + (k : ℤ) * (small.length e₀ : ℤ)) :
    ¬ FibreCover D small hN hL k hk member hClosed hScale := by
  refine not_fibreCover_of_large_scale D small hN hL k hk member hClosed hScale e₀ ?_
  have hmul : (Fintype.card member.target.V : ℤ) * (degree : ℤ) =
      (2 * genus member.data.sourceGraph + 2 * (degree : ℤ) - 4) * (degree : ℤ) := by
    rw [card_target_vertex_eq member]
  have key : ((Fintype.card member.target.V * degree : ℕ) : ℤ) + 1 <
      ((n + k * small.length e₀ : ℕ) : ℤ) := by
    push_cast
    rw [hmul]
    exact hlt
  exact_mod_cast key


/-! ## 3.  The natural route to (T), and the same count again -/

/-- **The placement, read as a contraction certificate.**  `bigDivisor` is by
definition the pushforward of `DegeneratePlacement.fibre` along this map; the
question is whether the map is `Valid`. -/
noncomputable def placementCertificate :
    GraphContractionCertificate member.data.sourceGraph
      (D.bigSpec (small.scale k hk) hN hL).graph :=
  GraphContractionCertificate.mk
    (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
      (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale))

/-- `bigDivisor` is the certificate pushforward of the member's own pullback
fibre.  This is `DegeneratePlacement.divisor` unfolded. -/
theorem pushDiv_placementCertificate_fibre (root : member.target.V) :
    (placementCertificate D small hN hL k hk member hClosed hScale).pushDiv
        (DegeneratePlacement.fibre (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member root) =
      bigDivisor D small hN hL k hk member hClosed hScale root := rfl

/-- **(T) from a source-side transport, through a valid placement.**  If the
placement is a valid contraction certificate and the pencil moves on the
member's own source graph by a script pulled back *twice* — once from the small
subdivision to the big one, once from the big one to the source graph — then (T)
holds.  `pushDiv_prin_pullScript` is the only step that needs validity, and it
is the only step that can turn a pushed-forward principal divisor back into a
principal one. -/
theorem fibreTransportFrom_of_placementTransport (root : member.target.V)
    (hValid : (placementCertificate D small hN hL k hk member hClosed hScale).Valid)
    (hSource : ∀ root' : member.target.V,
      ∃ tau : firing_script (small.scale k hk).graph,
        DegeneratePlacement.fibre (D.bigSpec (small.scale k hk) hN hL)
            (degenerateLength D small) member root' =
          DegeneratePlacement.fibre (D.bigSpec (small.scale k hk) hN hL)
              (degenerateLength D small) member root +
            prin member.data.sourceGraph
              ((placementCertificate D small hN hL k hk member hClosed hScale).pullScript
                ((ExpansionData.certificate D (small.scale k hk) hN hL).pullScript tau))) :
    FibreTransportFrom D small hN hL k hk member hClosed hScale root := by
  intro root'
  obtain ⟨tau, hEq⟩ := hSource root'
  refine ⟨tau, ?_⟩
  have hPush := congrArg
    (placementCertificate D small hN hL k hk member hClosed hScale).pushDiv hEq
  rw [GraphContractionCertificate.pushDiv_add,
    (placementCertificate D small hN hL k hk member hClosed hScale).pushDiv_prin_pullScript
      hValid] at hPush
  exact hPush

/-- **The placement cannot be surjective at large scale.**  Composed with the
contraction it would make the member's realization surjective onto the
small subdivision, which §2 refutes. -/
theorem realizationSurjective_of_sourcePoint_surjective
    (hCond : D.Conditions small.core)
    (hSurj : Function.Surjective
      (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed
        (fit D small hN hL k hk member hScale))) :
    RealizationSurjective D small hN hL k hk member hClosed hScale :=
  Function.Surjective.comp
    (ExpansionData.certificate_valid (D := D) (small := small.scale k hk)
      (hN := hN) (hL := hL) hCond).1 hSurj

theorem not_sourcePoint_surjective_of_card_lt (hCond : D.Conditions small.core)
    (hlt : Fintype.card member.target.V * degree <
      n + ∑ e : Fin p, (k * small.length e - 1)) :
    ¬ Function.Surjective
      (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed
        (fit D small hN hL k hk member hScale)) := fun hSurj ↦
  not_realizationSurjective_of_card_lt D small hN hL k hk member hClosed hScale hlt
    (realizationSurjective_of_sourcePoint_surjective D small hN hL k hk member hClosed
      hScale hCond hSurj)

/-- **The route of `fibreTransportFrom_of_placementTransport` is dead at large
scale.**  Validity of a contraction certificate includes surjectivity of its
vertex map. -/
theorem not_placementCertificate_valid_of_card_lt (hCond : D.Conditions small.core)
    (hlt : Fintype.card member.target.V * degree <
      n + ∑ e : Fin p, (k * small.length e - 1)) :
    ¬ (placementCertificate D small hN hL k hk member hClosed hScale).Valid :=
  fun hValid ↦ not_sourcePoint_surjective_of_card_lt D small hN hL k hk member hClosed
    hScale hCond hlt hValid.1


/-! ## 4.  What the count does not touch: the fused obligation -/

/-- **(TC): the transported cover.**  Exactly the hypothesis
`DegenerateFibreCover.pushableReachabilityAtRepresentatives_of_transportedCover`
consumes, specialized to `bigDivisor`, with (T) and (C) fused into one.

Unlike (C) it does **not** ask a chip to be at `b` already: the script `tau` may
depend on `b`, and the chip may be moved there.  The count of §2 therefore says
nothing about it. -/
def TransportedCover (root : member.target.V) : Prop :=
  ∀ b : (small.scale k hk).Vertex, ∃ tau : firing_script (small.scale k hk).graph,
    effective (bigDivisor D small hN hL k hk member hClosed hScale root +
        prin (D.bigSpec (small.scale k hk) hN hL).graph
          ((ExpansionData.certificate D (small.scale k hk) hN hL).pullScript tau)) ∧
      0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root +
          prin (D.bigSpec (small.scale k hk) hN hL).graph
            ((ExpansionData.certificate D (small.scale k hk) hN hL).pullScript tau)) b

/-- **(TC) suffices.**  The interface of `DegenerateFibreCover` takes it verbatim. -/
theorem forestContractionRank_of_transportedCover (hCond : D.Conditions small.core)
    (root : member.target.V)
    (hTC : TransportedCover D small hN hL k hk member hClosed hScale root) :
    ForestContractionRank D small hN hL k hk member hClosed hScale root := by
  refine rank_pushDivisor_of_pushableRepresentatives D (small.scale k hk) hN hL hCond
    (bigDivisor D small hN hL k hk member hClosed hScale root) ?_
  refine pushableReachabilityAtRepresentatives_of_transportedCover
    (ExpansionData.certificate D (small.scale k hk) hN hL) (fun b ↦ ?_)
  obtain ⟨tau, hEff, hPos⟩ := hTC b
  exact ⟨tau, hEff, by rwa [pushDivisor_eq_pushDiv D (small.scale k hk) hN hL] at hPos⟩

/-- **(T) and (C) imply (TC).**  So the refutation of (C) in §2 does not refute
(TC); it only shows that this particular sufficient route to it is unavailable
at large scale. -/
theorem transportedCover_of_transport_cover (root : member.target.V)
    (hTransport : FibreTransportFrom D small hN hL k hk member hClosed hScale root)
    (hCover : FibreCover D small hN hL k hk member hClosed hScale) :
    TransportedCover D small hN hL k hk member hClosed hScale root := by
  intro b
  obtain ⟨root', hPos⟩ := hCover b
  obtain ⟨tau, hTau⟩ := hTransport root'
  refine ⟨tau, ?_, ?_⟩
  · rw [← hTau]
    exact bigDivisor_effective D small hN hL k hk member hClosed hScale root'
  · rw [← hTau]
    exact hPos

end Obligations


/-! ## 5.  The shape that survives: a harmonic fibre on the small side -/

/-- **Rank one from a harmonic fibre.**  `IndexedHarmonicData`'s own
`rank_ge_one_of_target_one_chip_equiv` carries an unused `HasDegree` hypothesis;
this is the same statement without it, proved by the same three lines. -/
theorem rank_fibre_ge_one {G H : CFGraph} (f : MarkedGraphs.IndexedHarmonicData G H)
    (hPullback : f.PullbackPrincipalCompatible)
    (hTarget : MarkedGraphs.IndexedHarmonicData.TargetOneChipEquivalent H) (z : H.V) :
    rank G (f.fibre z) ≥ 1 := by
  apply rank_ge_one_of_vertex_certificates G (f.fibre z)
  intro x
  refine ⟨f.fibre (f.vertexMap x) - one_chip x, f.fibre_sub_one_chip_effective x, ?_⟩
  have hFibre : linear_equiv G (f.fibre z) (f.fibre (f.vertexMap x)) :=
    f.fibre_linear_equiv_of_target hPullback (hTarget z (f.vertexMap x))
  unfold linear_equiv at hFibre ⊢
  have hEq : f.fibre (f.vertexMap x) - one_chip x - (f.fibre z - one_chip x) =
      f.fibre (f.vertexMap x) - f.fibre z := by abel
  rw [hEq]
  exact hFibre

/-- **`ForestContractionRank` from a harmonic morphism on the small side.**  This is
`DegenerateBigDivisor`'s own reading of the rank statement — "the member's fibre is a
`g^1_d` on the metric graph the member realizes" — turned into a statement the
public harmonic interface discharges.

Note the target `T`: it is *not* `member.target`, because
`IndexedHarmonicData` forbids contracted source edges, so at scale `k` the
member's target tree has to be subdivided to match.  Connectedness and
genus zero survive subdivision, which is all the proof uses. -/
theorem forestContractionRank_of_harmonicFibre {n p N Q degree : ℕ}
    (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
    (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
    (hClosed : member.Closed) (hScale : memberScale member = k)
    (root : member.target.V) {T : CFGraph}
    (f : MarkedGraphs.IndexedHarmonicData (small.scale k hk).graph T)
    (hPullback : f.PullbackPrincipalCompatible)
    (hConn : graph_connected T) (hGenus : genus T = 0) (z : T.V)
    (hFibre : f.fibre z = ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
      (bigDivisor D small hN hL k hk member hClosed hScale root)) :
    ForestContractionRank D small hN hL k hk member hClosed hScale root := by
  show rank (small.scale k hk).graph _ ≥ 1
  rw [← hFibre]
  exact rank_fibre_ge_one f hPullback
    (MarkedGraphs.IndexedHarmonicData.targetOneChipEquivalent_of_connected_genus_zero
      T hConn hGenus) z

end DraismaVargas.Count.DegenerateTransport
