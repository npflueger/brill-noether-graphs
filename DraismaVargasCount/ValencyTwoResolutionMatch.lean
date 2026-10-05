module

public import DraismaVargasCount.ValencyTwoSplit
public import DraismaVargasCount.ValencyThreeResolutionMatch

@[expose] public section

/-!
# Valency-two resolution match: stage 4 at valency two, in general

**Source.**  Vargas, Part II (arXiv:2609.09109), the valency-two limits, Case `{v2-nd4}`
(`subsec-case-v2`).  The plan: rigidity from `resolutionMatch` plus
`ValencyThreeRigidity.frameIso_of_columns`; exhaustion onto a position from
`M11StarExhaustionProof.nonempty_transportFree_of_rel`.  Builds on `ValencyTwoSplit` (the fibre
pictures, `Split`, `Reads`, `ResolutionMatch` as a named residual) and the valency-three
`ValencyThreeResolutionMatch` (whose counting lemmas, `MergeRel`-free transports and
`exists_perm_image` are reused).  It is part of the type-change step, step 3 of `Assembly`;
the five stages are those of `ValencyTwoSplit`.

## The result, in one paragraph

`ValencyTwoSplit.ResolutionMatch core y degree` holds **at every core, request and degree, with
no hypothesis** (`resolutionMatch`), hence `ValencyTwoSplit.SplitRigidity` at every facet
request over a connected core with `3 ≤ n` (`splitRigidity`).  Read on every merged class, the
incoming resolution of a valency-two cover is fixed by its limit and its split.  **At a `(2,2)`
split** (§3): off the anchor every class is unramified, so the merged class is one class of
everything (`rel_off`, via `ValencyThreeResolutionMatch.pv_eq_merged`); on the anchor each endpoint partition is
its direction's partition with the non-pass survivor classes merged (`rel_on`: the trivalent
constituent `A_x` is the union of its survivors' classes, a pass-through is one class), and the
regrown occurrence is the common refinement of the two endpoint partitions (`contracted_rel`,
because the pruned fibre is a tree without multiple edges, `eq_of_same_ends`).  **At a leaf
split** (§4): every occurrence over the contracted edge has index one (`index_one`), so the
regrown occurrence is discrete (`contracted_rel_leaf`); the leaf endpoint's partition is discrete
but for the fold, a pair `{ℓ₁, ℓ₂}` of anchor sheets over different trivalent constituents
(`leaf_rel`); the trivalent endpoint's partition is the merged one off the anchor and one class
of each wall occurrence on it (`tri_rel`); paired survivors span the same sheets
(`paired_rel_iff`).  **The transports** (§5) are then written down directly: at `(2,2)` the two
directions' permutations for the two endpoints, and for the regrown occurrence the left one
corrected inside `A_l` by a permutation moving the right pass-through class
(`transport_div`); at a leaf split one direction's permutation for the trivalent side and, for
the leaf side and the regrown occurrence, the same corrected by two swaps that send the fold to
the fold (`transport_leaf`).  No realignment of the limit isomorphism is needed at valency two:
`ψ` itself carries the transport.  A `(2,2)` cover and a leaf cover never read the same split
(`not_leafCover_of_div`, `leafCover_of_leaf`).

## What is proved

* §1 `two_le_num_edges`, **`eq_of_same_ends`** (no multiple edges in the pruned fibre).
* §2 `survive` (no dangling occurrence at the anchor, any valency-two split),
  `sourceVertexMap_endpoint`, `endpoint_mem_fib`.
* §3 `NP`, `exists_ram_sheet`, `contracted_block_eq_off`, **`rel_off`**, `exists_other_edge`,
  `sourceEndpoint_eq_of_rel`, `side_of_target`, **`rel_on`**, **`contracted_rel`**.
* §4 `eq_of_blockCard_one`, `exists_fold`, **`index_one`**, `contracted_rel_leaf`,
  `size_one_of_ne_fold`, **`leaf_rel`**, **`tri_rel`**, **`paired_rel_iff`**.
* §5 **`transport_div`**, `swap_rel`, **`transport_leaf`** (abstract, in limit coordinates).
* §6 `Placed`, **`resolution_eq`**, `right_foldEdge`, `right_foldEdge_a`/`_b`,
  `foldEdge_mem_wall`, `eq_foldEdge_unfold`, `limit_edgePartition`.
* §7 `NPlim`, `label_sheet`, `label_unfold`, `unfoldEdge_injective`, `np_iff_nplim`,
  `side_rel`, `np_iff_nd`, `np_or`, `np_pass`, `side_rel_lim`, **`div_package`**.
* §8 `tri_ndOver_nonempty`, **`leaf_package`**, `paired_rel_lim`, `exists_label_partner`,
  `wall_at_v`, `placed_true`.
* §9 `mem_wall_map`, `label_target_map`, `label_sheet_map`, `nplim_map`,
  **`transport_divDiv`**, **`transport_leafLeaf`**.
* §10 `not_leafCover_of_div`, `leafCover_of_leaf`, **`resolutionMatch`**, **`splitRigidity`**.

## Hypotheses

* `resolutionMatch` has no hypothesis beyond its binders.
* `splitRigidity` keeps stage 5's inputs `core.Connected`, `3 ≤ n`, `y e₀ = 0`
  (`ValencyThreeRigidity.frameIso_of_columns`), all true at a facet point of a cubic core.
* Stage 3 (`ValencyTwoSplit.PairingMatch`) is not treated here (see `ValencyTwoPairing`).
* No new `Prop` on the critical path (`NP`, `NPlim`, `Placed` are sheet predicates and an
  abbreviation of the existing placement disjunction).
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.

## Two expectations, checked

* *"Exhaustion onto a position needs `nonempty_transportFree_of_rel` plus the facet-form pendant
  realignment `ValencyThreeResolutionMatch.pendant_at_wall_forest`"*: the first **holds**; the
  second is **not needed** at valency two.  The only freedom a leaf split has that the limit does
  not see is which sheet of each trivalent constituent the fold uses; that is absorbed by two
  swaps inside the endpoint and regrown permutations, which are free, so the limit isomorphism
  is never re-chosen.
* *"There is one class of each type"*: at valency two every class at a labelled metric limit
  reading a given split is the same class (`splitRigidity`); together with
  `ValencyTwoSplit.split_eq_of_paired`, one class per pairing -- Part II's count, modulo stage 3.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.ValencyTwoResolutionMatch

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification W4StableSource WallDegeneration
open FullDimensionalSource PrunedFibreValency PrunedFibreTree FullContractionFibre
open ValencyThreeSplit (ndAt mem_ndAt card_ndAt size ram fib intl mem_fib_iff intl_ends
  mem_intl_of_ndAt ndOver mem_ndOver bdAt mem_bdAt limA side_of_huv target_mem_incidentEdges
  contracted_mem_incidentEdges not_incident_both ram_le_targetChange ram_nonneg)
open ValencyTwoSplit (AnchorInput DivInput LeafInput Labelling lift lift_ne Paired PassAt
  PairedE ram_add_ram_le)

/-! ## 1.  The pruned fibre has no multiple edges -/

section Tree

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)

/-- The number of source occurrences joining two source vertices. -/
theorem two_le_num_edges {X Y : data.SourceVertex} {e e' : data.SourceEdge} (hne : e ≠ e')
    (hXY : X ≠ Y) (heX : Incident data e X) (heY : Incident data e Y)
    (he'X : Incident data e' X) (he'Y : Incident data e' Y) :
    2 ≤ num_edges data.sourceGraph X Y := by
  classical
  have hends : ∀ f : data.SourceEdge, Incident data f X → Incident data f Y →
      data.sourceEnds f = (X, Y) ∨ data.sourceEnds f = (Y, X) := by
    intro f hX hY
    rcases hX with h | h <;> rcases hY with h' | h'
    · exact absurd (h.symm.trans h') hXY
    · left; exact Prod.ext h h'
    · right; exact Prod.ext h' h
    · exact absurd (h.symm.trans h') hXY
  unfold num_edges
  change 2 ≤ Multiset.card (((Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds).filter
    fun p ↦ p = (X, Y) ∨ p = (Y, X))
  rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val, Finset.card_val]
  have hsub : ({e, e'} : Finset data.SourceEdge) ⊆ Finset.univ.filter
      (fun f ↦ data.sourceEnds f = (X, Y) ∨ data.sourceEnds f = (Y, X)) := by
    intro f hf
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hends _ heX heY
    · rw [Finset.mem_singleton.mp hf]; exact hends _ he'X he'Y
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  exact this

/-- **No two surviving internal occurrences join the same two constituents**: the pruned
fibre is a tree (connected with the tree count), so it has no multiple edges. -/
theorem eq_of_same_ends (hForest : ContractionForest data a b contracted)
    {X Y : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) (hXY : X ≠ Y) {e e' : data.SourceEdge}
    (heX : Incident data e X) (heY : Incident data e Y)
    (he'X : Incident data e' X) (he'Y : Incident data e' Y) : e = e' := by
  classical
  by_contra hne
  have hNe : (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).Nonempty :=
    ⟨X, hX⟩
  have hconn := activeFibreGraph_connected data hc hab hOne (mergedVertex data hc hab hOne block) hNe
  have hcount : (activeFibreGraph data hc hab hOne (mergedVertex data hc hab hOne block)
      hNe).edges.card + 1 =
      Fintype.card (activeFibreGraph data hc hab hOne (mergedVertex data hc hab hOne block)
        hNe).V := by
    rw [activeFibreGraph_edge_card, activeFibreGraph_vertex_card]
    exact internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne hForest block hNe
  obtain ⟨-, hle⟩ := InducedFibreTreeCount.underlying_tree_and_num_edges_le_one _ hconn hcount
  have h1 := hle ⟨X, hX⟩ ⟨Y, hY⟩
  have h1' : num_edges data.sourceGraph X Y ≤ 1 := by
    have := Utilities.num_edges_inducedSubgraph data.sourceGraph
      (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)) hNe
      ⟨X, hX⟩ ⟨Y, hY⟩
    exact this ▸ h1
  have h2 := two_le_num_edges data hne hXY heX heY he'X he'Y
  omega

end Tree

/-! ## 2.  General facts at a valency-two anchor -/

section Anchor

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (H : AnchorInput data hc hab hOne block)

include fd H in
/-- **No dangling occurrence at the anchor**: `N(A) = r₀(A) + 2 = 4 = nd(A)`, so every
non-contracted occurrence at a constituent of the anchor fibre survives. -/
theorem survive {X : data.SourceVertex}
    (hX : sourceVertexMap data hc hab hOne X = mergedVertex data hc hab hOne block)
    {e : data.SourceEdge} (he : Incident data e X) (hT : e.1.1 ≠ contracted) :
    ¬ IsDangling data e := by
  classical
  have hram := NonTrivalentValencyTwoRigidity.localRamification_eq_two data fd hc hab hOne
    H.forest H.compat (W2R1Target.TwoStar.of_card H.valency) block H.nd4
  have hN := NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form
    (contractDatum data hc hab hOne) (mergedVertex data hc hab hOne block)
  have hval : (GluingDatum.incidentEdges (mergedVertex data hc hab hOne block).1.1).card = 2 :=
    H.valency
  rw [hval] at hN
  have hEq : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) =
      Fintype.card (IncidentSourceEdge (contractDatum data hc hab hOne)
        (mergedVertex data hc hab hOne block)) := by
    have hr : (contractDatum data hc hab hOne).localRamification
        (mergedVertex data hc hab hOne block).1.1
        ⟨(mergedVertex data hc hab hOne block).1.2, (mergedVertex data hc hab hOne block).2⟩ =
        2 := hram
    rw [hr] at hN
    have h4 : nonDanglingValency (contractDatum data hc hab hOne)
        (mergedVertex data hc hab hOne block) = 4 := H.nd4
    rw [h4]
    push_cast at hN
    omega
  intro hBad
  have hInc : Incident (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne ⟨e, hT⟩)
      (mergedVertex data hc hab hOne block) := by
    unfold Incident
    rw [sourceEnds_sourceEdgeMap]
    rcases he with h | h
    · left; rw [h]; exact hX
    · right; rw [h]; exact hX
  exact ValencyTwoSplit.not_isDangling_of_nd_eq _ _ hEq hInc (H.compat.1 ⟨e, hT⟩ hBad)

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A sheet of the anchor block, read at an endpoint, is a constituent of the anchor fibre. -/
theorem sourceVertexMap_endpoint {x : target.V} (hx : x = a ∨ x = b) {s : Fin degree}
    (hs : (mergedPartition data a b).Rel block.1 s) :
    sourceVertexMap data hc hab hOne (data.sourceEndpoint x s) =
      mergedVertex data hc hab hOne block := by
  have h := (mem_fibreVertices_mergedVertex_iff data hc hab hOne block
    (data.sourceEndpoint x s)).mpr ⟨hx, ?_⟩
  · exact (mem_fibreVertices data hc hab hOne _ _).mp h
  · change (mergedPartition data a b).repr ((data.vertexPartition x).repr s) = block.1
    have href : (data.vertexPartition x).Refines (mergedPartition data a b) := by
      rcases hx with rfl | rfl
      · exact vertexPartition_refines_mergedPartition data _ _
      · exact vertexPartition_refines_mergedPartition_right data _ _
    have h1 : (mergedPartition data a b).Rel ((data.vertexPartition x).repr s) s :=
      href.rel ((data.vertexPartition x).rel_repr_left s)
    rw [h1, ← hs, block.2]

include fd H in
/-- **Every constituent of the anchor fibre over an endpoint with a non-contracted target
occurrence is active.** -/
theorem endpoint_mem_fib {x : target.V} (hx : x = a ∨ x = b) {t : target.edges}
    (ht : t ∈ GluingDatum.incidentEdges x) (htc : t ≠ contracted) {s : Fin degree}
    (hs : (mergedPartition data a b).Rel block.1 s) :
    data.sourceEndpoint x s ∈ fib data hc hab hOne block := by
  rw [fib, mem_activeFibreVertices]
  refine ⟨sourceVertexMap_endpoint hx hs, ?_⟩
  have hinc := incident_sourceEdge_sourceEndpoint data x t ht s
  exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident data
    (survive fd H (sourceVertexMap_endpoint hx hs) hinc htc) hinc

end Anchor

/-! ## 3.  The incoming resolution at a `(2,2)` split, on every merged class -/

section Divalent

open ValencyThreeResolutionMatch (pv_eq_merged ram_zero_of_not_rel block_eq_of_unram)

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (H : AnchorInput data hc hab hOne block) (Hd : DivInput data hc hab hOne block)
  (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- The survivors of the non-pass labels in one direction, as a sheet predicate: the sheets of
the trivalent constituent's boundary classes there. -/
def NP (t : target.edges) (s : Fin degree) : Prop :=
  ∃ i, (lift L i).1.1 = t ∧ ¬ PassAt L i ∧ (data.edgePartition t).Rel (lift L i).1.2 s

include fd Hd in
/-- The ramified sheet over each endpoint of a `(2,2)` split lies in the anchor. -/
theorem exists_ram_sheet {x : target.V} (hx : x = a ∨ x = b) :
    ∃ r : Fin degree, localRamificationAt data x r = 1 ∧
      (mergedPartition data a b).Rel block.1 r := by
  obtain ⟨Ra, Rb, hRa, hRb, hRaa, hRbb, hRa3, hRb3⟩ := Hd.exists_R fd
  have key : ∀ R : data.SourceVertex, R ∈ fib data hc hab hOne block → R.1.1 = x →
      nonDanglingValency data R = 3 → ∃ r : Fin degree, localRamificationAt data x r = 1 ∧
        (mergedPartition data a b).Rel block.1 r := by
    intro R hR hRx hR3
    have hram := Hd.ram_eq_nd fd hR
    rw [hR3] at hram
    obtain ⟨-, hrepr, -⟩ := (mem_fib_iff data hc hab hOne block R).mp hR
    obtain ⟨⟨x', r⟩, hr⟩ := R
    simp only at hRx
    subst hRx
    refine ⟨r, ?_, ?_⟩
    · change data.localRamification x' ⟨r, hr⟩ = 1
      have : ram data ⟨(x', r), hr⟩ = 1 := by rw [hram]; norm_num
      exact this
    · change (mergedPartition data a b).repr block.1 = (mergedPartition data a b).repr r
      rw [block.2]; exact hrepr.symm
  rcases hx with rfl | rfl
  · exact key Ra hRa hRaa hRa3
  · exact key Rb hRb hRbb hRb3

include fd Hd in
/-- **Off the anchor every merged class is one class of everything**: its constituents are
unramified, hence one class of each occurrence (`block_eq_of_unram`), and the forest count
(`pv_eq_merged`) makes the other side the whole merged class. -/
theorem contracted_block_eq_off {x : target.V} (hx : x = a ∨ x = b) {s : Fin degree}
    (hs : ¬ (mergedPartition data a b).Rel block.1 s) :
    (data.edgePartition contracted).block s = (data.vertexPartition x).block s := by
  obtain ⟨r, hr, hrA⟩ := exists_ram_sheet fd Hd hx
  have hx2 : (GluingDatum.incidentEdges x).card = 2 := by
    rcases hx with rfl | rfl
    · exact Hd.a2
    · exact Hd.b2
  have hch : data.targetChange x = 1 := by
    rcases hx with rfl | rfl
    · exact Hd.cha
    · exact Hd.chb
  have href : (data.vertexPartition x).Refines (mergedPartition data a b) := by
    rcases hx with rfl | rfl
    · exact vertexPartition_refines_mergedPartition data _ _
    · exact vertexPartition_refines_mergedPartition_right data _ _
  have hrs : ¬ (data.vertexPartition x).Rel r s := fun h ↦ hs (hrA.trans (href.rel h))
  exact block_eq_of_unram data hx2 s (ram_zero_of_not_rel data fd.valid hch r s hr hrs)
    contracted (contracted_mem_incidentEdges hc hx)

include fd Hd in
theorem rel_off {x : target.V} (hx : x = a ∨ x = b) {s : Fin degree}
    (hs : ¬ (mergedPartition data a b).Rel block.1 s) (t : Fin degree) :
    (data.vertexPartition x).Rel s t ↔ (mergedPartition data a b).Rel s t := by
  have huv : ((if x = a then b else a) = a ∧ x = b) ∨ ((if x = a then b else a) = b ∧ x = a) := by
    rcases hx with rfl | rfl
    · right; simp
    · left; simp [Ne.symm hab]
  set y := if x = a then b else a
  have hy : y = a ∨ y = b := by rcases huv with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
  refine pv_eq_merged data hc hab Hd.forest huv s (fun z hz z' _ hzz' ↦ ?_) t
  have hzA : ¬ (mergedPartition data a b).Rel block.1 z := by
    intro h
    rw [SheetPartition.mem_block_iff] at hz
    exact hs (h.trans hz.symm)
  have hb := contracted_block_eq_off fd Hd hy hzA
  rw [← SheetPartition.mem_block_iff, ← hb, SheetPartition.mem_block_iff] at hzz'
  exact hzz'

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A divalent endpoint has a non-contracted target occurrence. -/
theorem exists_other_edge {x : target.V} (hx2 : (GluingDatum.incidentEdges x).card = 2) :
    ∃ t₀ ∈ GluingDatum.incidentEdges x, t₀ ≠ contracted := by
  classical
  have : 1 < (GluingDatum.incidentEdges x).card := by omega
  obtain ⟨t₀, ht₀, hne⟩ := Finset.exists_mem_ne this contracted
  exact ⟨t₀, ht₀, hne⟩

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem sourceEndpoint_eq_of_rel {x : target.V} {s t : Fin degree}
    (h : (data.vertexPartition x).Rel s t) : data.sourceEndpoint x t = data.sourceEndpoint x s :=
  Subtype.ext (Prod.ext rfl h.symm)

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A non-contracted target occurrence at one endpoint does not meet the other. -/
theorem side_of_target {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {x : target.V} (hx : x = a ∨ x = b) {t₀ : target.edges}
    (ht : t₀ ∈ GluingDatum.incidentEdges x) (htc : t₀ ≠ contracted)
    (hXt : t₀ ∈ GluingDatum.incidentEdges X.1.1) : X.1.1 = x := by
  rcases ((mem_fib_iff data hc hab hOne block X).mp hX).1 with h | h <;> rcases hx with rfl | rfl
  · exact h
  · exfalso; rw [h] at hXt
    exact ValencyThreeSplit.not_mem_incidentEdges_other hc hab hOne (Or.inr ⟨rfl, rfl⟩) ht htc hXt
  · exfalso; rw [h] at hXt
    exact ValencyThreeSplit.not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) ht htc hXt
  · exact h

include fd H Hd in
/-- **The endpoint partition on the anchor** at a `(2,2)` split: two anchor sheets are one
class over `x` exactly when they are one class of `x`'s non-contracted occurrence `t₀`, or both
lie in classes of non-pass survivors there (the trivalent constituent `A_x`; a pass-through is
one class of `t₀`). -/
theorem rel_on {x : target.V} (hx : x = a ∨ x = b) {t₀ : target.edges}
    (ht : t₀ ∈ GluingDatum.incidentEdges x) (htc : t₀ ≠ contracted) {s : Fin degree}
    (hs : (mergedPartition data a b).Rel block.1 s) (t : Fin degree) :
    (data.vertexPartition x).Rel s t ↔ (mergedPartition data a b).Rel s t ∧
      ((data.edgePartition t₀).Rel s t ∨ (NP L t₀ s ∧ NP L t₀ t)) := by
  classical
  have href : (data.vertexPartition x).Refines (mergedPartition data a b) := by
    rcases hx with rfl | rfl
    · exact vertexPartition_refines_mergedPartition data _ _
    · exact vertexPartition_refines_mergedPartition_right data _ _
  have hEref := edgePartition_refines_of_mem_incidentEdges data x t₀ ht
  -- the home of a boundary class over `t₀`
  have hbd : ∀ z : Fin degree, (mergedPartition data a b).Rel block.1 z →
      data.sourceEndpoint x z ∈ fib data hc hab hOne block ∧
        data.sourceEdge t₀ z ∈ bdAt data contracted (data.sourceEndpoint x z) := by
    intro z hz
    have hX := endpoint_mem_fib fd H hx ht htc hz
    have hinc := incident_sourceEdge_sourceEndpoint data x t₀ ht z
    refine ⟨hX, (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨survive fd H
      (sourceVertexMap_endpoint hx hz) hinc htc, hinc⟩, htc⟩⟩
  constructor
  · intro hst
    refine ⟨href.rel hst, ?_⟩
    obtain ⟨hX, hf⟩ := hbd s hs
    have hXt : data.sourceEndpoint x t = data.sourceEndpoint x s := sourceEndpoint_eq_of_rel hst
    have hg := (hbd t (hs.trans (href.rel hst))).2
    rw [hXt] at hg
    obtain ⟨i, hi⟩ := ValencyTwoSplit.exists_lift_eq L H.compat H.nd4 hX hf
    obtain ⟨j, hj⟩ := ValencyTwoSplit.exists_lift_eq L H.compat H.nd4 hX hg
    by_cases h2 : nonDanglingValency data (data.sourceEndpoint x s) = 2
    · left
      have h1 := (Hd.pass_cards fd hX h2).2
      have hfg : data.sourceEdge t₀ s = data.sourceEdge t₀ t :=
        Finset.card_le_one.mp (le_of_eq h1) _ hf _ hg
      exact congrArg (fun e : data.SourceEdge ↦ e.1.2) hfg
    · right
      have hnp : ∀ k, lift L k ∈ bdAt data contracted (data.sourceEndpoint x s) → ¬ PassAt L k :=
        fun k hk hp ↦ h2 ((ValencyTwoSplit.passAt_iff_home L hX hk).mp hp)
      refine ⟨⟨i, by rw [hi]; rfl, hnp i (hi ▸ hf), ?_⟩, ⟨j, by rw [hj]; rfl, hnp j (hj ▸ hg), ?_⟩⟩
      · rw [hi]; exact (data.edgePartition t₀).rel_repr_left s
      · rw [hj]; exact (data.edgePartition t₀).rel_repr_left t
  · rintro ⟨hM, hE | ⟨⟨i, hit, hip, his⟩, ⟨j, hjt, hjp, hjt'⟩⟩⟩
    · exact hEref.rel hE
    · -- both homes are the trivalent constituent over `x`
      have home : ∀ k z, (lift L k).1.1 = t₀ → ¬ PassAt L k →
          (data.edgePartition t₀).Rel (lift L k).1.2 z →
          ∃ Xk ∈ fib data hc hab hOne block, Xk.1.1 = x ∧ nonDanglingValency data Xk = 3 ∧
            (data.vertexPartition x).Rel Xk.1.2 z := by
        intro k z hkt hkp hkz
        obtain ⟨Xk, hXk, hk⟩ := ValencyTwoSplit.exists_home L H.compat k
        have hkinc := ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hk).1).2
        have hXx : Xk.1.1 = x := side_of_target hXk hx ht htc
          (hkt ▸ target_mem_incidentEdges data hkinc)
        refine ⟨Xk, hXk, hXx, ?_, ?_⟩
        · have hb := DivInput.nd_bounds fd hXk
          have := (ValencyTwoSplit.passAt_iff_home L hXk hk).not.mp hkp
          omega
        · have hrel := ((incident_iff_target_mem_and_rel data _ _).mp hkinc).2
          rw [hXx] at hrel
          exact hrel.trans (hEref.rel (hkt ▸ hkz))
      obtain ⟨Xi, hXi, hXix, hXi3, hXis⟩ := home i s hit hip his
      obtain ⟨Xj, hXj, hXjx, hXj3, hXjt⟩ := home j t hjt hjp hjt'
      have hEq := Hd.eq_of_nd_three fd hXi hXj hXi3 hXj3 (hXix.trans hXjx.symm)
      rw [hEq] at hXis
      exact hXis.symm.trans hXjt

include fd H Hd in
/-- **The regrown occurrence is the common refinement of the two endpoint partitions** at a
`(2,2)` split: off the anchor all three are the merged class; on the anchor two sheets with the
same pair of endpoint classes lie over one internal occurrence, since the pruned fibre has no
multiple edges (`eq_of_same_ends`). -/
theorem contracted_rel (s t : Fin degree) :
    (data.edgePartition contracted).Rel s t ↔
      (data.vertexPartition a).Rel s t ∧ (data.vertexPartition b).Rel s t := by
  classical
  have hra := ValencyThreeResolutionMatch.contracted_refines_u data hc hab
    (u := a) (v := b) (Or.inl ⟨rfl, rfl⟩)
  have hrb := ValencyThreeResolutionMatch.contracted_refines_v data hc hab
    (u := a) (v := b) (Or.inl ⟨rfl, rfl⟩)
  constructor
  · intro h; exact ⟨hra.rel h, hrb.rel h⟩
  · rintro ⟨ha, hb⟩
    by_cases hs : (mergedPartition data a b).Rel block.1 s
    · obtain ⟨ta, hta, htac⟩ := exists_other_edge (contracted := contracted) Hd.a2
      obtain ⟨tb, htb, htbc⟩ := exists_other_edge (contracted := contracted) Hd.b2
      have hX := endpoint_mem_fib fd H (Or.inl rfl) hta htac hs
      have hY := endpoint_mem_fib fd H (Or.inr rfl) htb htbc hs
      have hXY : data.sourceEndpoint a s ≠ data.sourceEndpoint b s := fun h ↦
        hab (congrArg (fun X : data.SourceVertex ↦ X.1.1) h)
      have hca := contracted_mem_incidentEdges hc (Or.inl rfl)
      have hcb := contracted_mem_incidentEdges hc (Or.inr rfl)
      have h1 := incident_sourceEdge_sourceEndpoint data a contracted hca s
      have h2 := incident_sourceEdge_sourceEndpoint data b contracted hcb s
      have h3 := incident_sourceEdge_sourceEndpoint data a contracted hca t
      have h4 := incident_sourceEdge_sourceEndpoint data b contracted hcb t
      rw [sourceEndpoint_eq_of_rel ha] at h3
      rw [sourceEndpoint_eq_of_rel hb] at h4
      have hEq := eq_of_same_ends data hc hab hOne block H.forest hX hY hXY h1 h2 h3 h4
      exact congrArg (fun e : data.SourceEdge ↦ e.1.2) hEq
    · have hbk := contracted_block_eq_off fd Hd (Or.inl rfl) hs
      rw [← SheetPartition.mem_block_iff, hbk, SheetPartition.mem_block_iff]
      exact ha

end Divalent

/-! ## 4.  The incoming resolution at a leaf split, on every merged class -/

section Leaf

open ValencyThreeResolutionMatch (pv_eq_merged rel_iff_of_index)

theorem eq_of_blockCard_one {d : ℕ} {P : SheetPartition d} {s t : Fin d} (h1 : P.blockCard s = 1)
    (h : P.Rel s t) : s = t := by
  have hs : s ∈ P.block s := (P.mem_block_iff s s).mpr rfl
  have ht : t ∈ P.block s := (P.mem_block_iff s t).mpr h
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
  rw [hx, Finset.mem_singleton] at hs ht
  exact hs.trans ht.symm

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  {u v : target.V}
  (H : AnchorInput data hc hab hOne block) (Hl : LeafInput data hc hab hOne block u v)
  (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

include fd H Hl in
/-- **The fold**: an active constituent over the leaf. -/
theorem exists_fold : ∃ F ∈ fib data hc hab hOne block, F.1.1 = u := by
  classical
  let L₀ : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block) :=
    (ValencyTwoSplit.nonempty_labelling _ _ H.nd4).some
  obtain ⟨Y, hY, h0⟩ := ValencyTwoSplit.exists_home L₀ H.compat 0
  obtain ⟨hYv, hY3, hYr⟩ := Hl.home fd hY h0
  have hbd : (bdAt data contracted Y).card ≤ 2 := by
    obtain ⟨t₁, t₂, t₃, -⟩ := Finset.card_eq_three.mp Hl.v3
    by_contra h
    have hlt : 2 < (bdAt data contracted Y).card := by omega
    -- three boundary survivors over two non-contracted directions
    have htargets : ∀ f ∈ bdAt data contracted Y, f.1.1 ∈
        (GluingDatum.incidentEdges v).erase contracted := by
      intro f hf
      obtain ⟨hf1, hf2⟩ := (mem_bdAt data _ _).mp hf
      have := target_mem_incidentEdges data ((mem_ndAt data _ _).mp hf1).2
      rw [hYv] at this
      exact Finset.mem_erase.mpr ⟨hf2, this⟩
    have hcard : ((GluingDatum.incidentEdges v).erase contracted).card = 2 := by
      rw [Finset.card_erase_of_mem (contracted_mem_incidentEdges hc (side_of_huv hab Hl.huv).2.1),
        Hl.v3]
    have hinj : Set.InjOn (fun f : data.SourceEdge ↦ f.1.1) (bdAt data contracted Y) := by
      intro f hf g hg hfg
      exact ValencyThreeSplit.eq_of_ram_zero data fd hYr ((mem_bdAt data _ _).mp hf).1
        ((mem_bdAt data _ _).mp hg).1 hfg
    have := Finset.card_le_card_of_injOn _ htargets hinj
    omega
  have hsplit := ValencyThreeSplit.card_ndAt_split data (contracted := contracted) Y
  obtain ⟨e, he⟩ : (ndOver data Y contracted).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨heY, heT⟩ := (mem_ndOver data _ _ _).mp he
  have heI := mem_intl_of_ndAt data hc hab hOne block hY heY heT
  obtain ⟨Q, hQ, -, hQs, -⟩ := DivInput.exists_other_end heI ((mem_ndAt data _ _).mp heY).2
  refine ⟨Q, hQ, ?_⟩
  rcases Hl.side hQ with h | h
  · exact h
  · exact absurd (h.trans hYv.symm) hQs

include fd H Hl in
/-- **The fold is a two-sheet block with two single-sheet occurrences**, and every other block
over the leaf is a single sheet with one single-sheet occurrence; so every occurrence over the
contracted target edge has index one. -/
theorem index_one {e : data.SourceEdge} (he : e.1.1 = contracted) : data.sourceEdgeIndex e = 1 := by
  classical
  obtain ⟨F, hF, hFu⟩ := exists_fold fd H Hl
  have hu1 : ∀ X : data.SourceVertex, X.1.1 = u →
      (GluingDatum.incidentEdges X.1.1).card = 1 := fun X hX ↦ by rw [hX]; exact Hl.u1
  have huw := (side_of_huv hab Hl.huv).1
  -- the `u`-end of `e`
  set X : data.SourceVertex := data.sourceEndpoint u e.1.2 with hXdef
  have hXu : X.1.1 = u := rfl
  have hcu : contracted ∈ GluingDatum.incidentEdges u := contracted_mem_incidentEdges hc huw
  have heX : Incident data e X := by
    have := incident_sourceEdge_sourceEndpoint data u contracted hcu e.1.2
    rwa [← he, GluingDatum.sourceEdge_self] at this
  have hN := NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data X
  have hLe := StableLocalProperties.card_incidentSourceEdge_le_blockCard_of_target_leaf data X
    (hu1 X hXu)
  rw [hu1 X hXu] at hN
  have hN' : (Fintype.card (IncidentSourceEdge data X) : ℤ) =
      ram data X + 2 - size data X := by rw [hN]; unfold ram size; push_cast; ring
  have hr := ram_le_targetChange data fd X
  rw [hXu, Hl.chu] at hr
  -- every occurrence at `X` has index at least one, and they add up to `|X|`
  have hsum := ValencyThreeSplit.sum_over_eq_size data X contracted (by rw [hXu]; exact hcu)
  have hmem : e ∈ Finset.univ.filter (fun f : data.SourceEdge ↦ Incident data f X ∧ f.1.1 = contracted) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, heX, he⟩
  have hcardS : ((Finset.univ.filter fun f : data.SourceEdge ↦
      Incident data f X ∧ f.1.1 = contracted).card : ℤ) =
      Fintype.card (IncidentSourceEdge data X) := by
    have : (Finset.univ.filter fun f : data.SourceEdge ↦ Incident data f X ∧ f.1.1 = contracted) =
        Finset.univ.filter fun f : data.SourceEdge ↦ Incident data f X := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.1
      · intro h
        refine ⟨h, ?_⟩
        have := target_mem_incidentEdges data h
        rw [hXu] at this
        obtain ⟨t, ht⟩ := Finset.card_eq_one.mp Hl.u1
        rw [ht, Finset.mem_singleton] at this hcu
        exact this.trans hcu.symm
    have e1 : (Finset.univ.filter fun f : data.SourceEdge ↦ Incident data f X).card =
        Fintype.card {f : data.SourceEdge // Incident data f X} :=
      (Fintype.card_subtype (fun f : data.SourceEdge ↦ Incident data f X)).symm
    have e2 : Fintype.card {f : data.SourceEdge // Incident data f X} =
        Fintype.card (IncidentSourceEdge data X) :=
      Fintype.card_congr (Equiv.refl _)
    rw [this]
    exact_mod_cast e1.trans e2
  have hsplit := Finset.sum_erase_add _ (fun f ↦ (data.sourceEdgeIndex f : ℤ)) hmem
  have hrest : ((Finset.univ.filter fun f : data.SourceEdge ↦
      Incident data f X ∧ f.1.1 = contracted).erase e).card ≤
      ∑ f ∈ (Finset.univ.filter fun f : data.SourceEdge ↦
        Incident data f X ∧ f.1.1 = contracted).erase e, (data.sourceEdgeIndex f : ℤ) :=
    ValencyThreeSplit.card_le_sum_index data _
  rw [Finset.card_erase_of_mem hmem] at hrest
  have hpos := StableLocalProperties.sourceEdgeIndex_pos data e
  have hr0 := ram_nonneg data fd X
  have hsz : (size data X : ℤ) = ((data.vertexPartition X.1.1).blockCard X.1.2 : ℤ) := rfl
  have hN1 : 1 ≤ (Finset.univ.filter fun f : data.SourceEdge ↦
      Incident data f X ∧ f.1.1 = contracted).card := Finset.card_pos.mpr ⟨e, hmem⟩
  by_cases hXF : X = F
  · -- the fold: `r ≥ 2`, `nd ≥ 2`, so `N = |X| = 2`
    have hr2 : 2 ≤ ram data X := by
      have := NonTrivalentValencyTwoRigidity.two_le_localRamification_of_target_leaf data
        fd.connected F (by rw [hFu]; exact Hl.u1) ((mem_fib_iff data hc hab hOne block F).mp hF).2.2
      rw [← hXF] at this
      exact this
    have hnd := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data X
    have hnd2 : 2 ≤ nonDanglingValency data X := by
      have := ValencyThreeSplit.nonDanglingValency_two_le data fd
        ((mem_fib_iff data hc hab hOne block F).mp hF).2.2
      rw [← hXF] at this
      exact this
    have : (2 : ℤ) ≤ Fintype.card (IncidentSourceEdge data X) := by exact_mod_cast hnd2.trans hnd
    omega
  · -- any other block over the leaf is unramified: `N = 2 - |X|`, so `|X| = 1`
    have hsum2 := ram_add_ram_le data fd.valid hXF (hXu.trans hFu.symm)
    rw [hXu, Hl.chu] at hsum2
    have hr2 : 2 ≤ ram data F :=
      NonTrivalentValencyTwoRigidity.two_le_localRamification_of_target_leaf data
        fd.connected F (by rw [hFu]; exact Hl.u1) ((mem_fib_iff data hc hab hOne block F).mp hF).2.2
    omega

include fd H Hl in
/-- **At a leaf split the regrown occurrence is discrete.** -/
theorem contracted_rel_leaf (s t : Fin degree) :
    (data.edgePartition contracted).Rel s t ↔ s = t := by
  constructor
  · intro h
    have h1 : data.sourceEdgeIndex (data.sourceEdge contracted s) = 1 := index_one fd H Hl rfl
    change ((data.edgePartition contracted).blockCard ((data.edgePartition contracted).repr s)) = 1
      at h1
    have hr1 := eq_of_blockCard_one h1 ((data.edgePartition contracted).rel_repr_left s)
    have hr2 := eq_of_blockCard_one h1 (((data.edgePartition contracted).rel_repr_left s).trans h)
    exact hr1.symm.trans hr2
  · rintro rfl; rfl

omit H in
include fd Hl in
/-- Every block over the leaf but the fold is a single sheet. -/
theorem size_one_of_ne_fold {F : data.SourceVertex} (hF : F ∈ fib data hc hab hOne block)
    (hFu : F.1.1 = u) {X : data.SourceVertex} (hXu : X.1.1 = u) (hXF : X ≠ F) :
    size data X = 1 := by
  have hsum2 := ram_add_ram_le data fd.valid hXF (hXu.trans hFu.symm)
  rw [hXu, Hl.chu] at hsum2
  have hr2 : 2 ≤ ram data F :=
    NonTrivalentValencyTwoRigidity.two_le_localRamification_of_target_leaf data
      fd.connected F (by rw [hFu]; exact Hl.u1) ((mem_fib_iff data hc hab hOne block F).mp hF).2.2
  have hN := NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data X
  have hu1 : (GluingDatum.incidentEdges X.1.1).card = 1 := by rw [hXu]; exact Hl.u1
  rw [hu1] at hN
  have hN' : (Fintype.card (IncidentSourceEdge data X) : ℤ) =
      ram data X + 2 - size data X := by rw [hN]; unfold ram size; push_cast; ring
  have hinc : Incident data (data.sourceEdge contracted X.1.2) X := by
    have := incident_sourceEdge_sourceEndpoint data X.1.1 contracted
      (by rw [hXu]; exact contracted_mem_incidentEdges hc (side_of_huv hab Hl.huv).1) X.1.2
    have hX : data.sourceEndpoint X.1.1 X.1.2 = X :=
      (data.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
    rwa [hX] at this
  have hpos : 0 < Fintype.card (IncidentSourceEdge data X) := Fintype.card_pos_iff.mpr ⟨⟨_, hinc⟩⟩
  have hr0 := ram_nonneg data fd X
  have hs := (data.vertexPartition X.1.1).blockCard_pos X.1.2
  have : (1 : ℤ) ≤ Fintype.card (IncidentSourceEdge data X) := by exact_mod_cast hpos
  have hsz : (size data X : ℤ) = ((data.vertexPartition X.1.1).blockCard X.1.2 : ℤ) := rfl
  omega

include fd H Hl in
/-- **The leaf endpoint's partition**: discrete except the fold, a pair `{ℓ₁, ℓ₂}` of anchor
sheets lying in different classes over the trivalent endpoint. -/
theorem leaf_rel : ∃ ℓ₁ ℓ₂ : Fin degree, ℓ₁ ≠ ℓ₂ ∧
    (mergedPartition data a b).Rel block.1 ℓ₁ ∧ (mergedPartition data a b).Rel block.1 ℓ₂ ∧
    ¬ (data.vertexPartition v).Rel ℓ₁ ℓ₂ ∧
    ∀ s t, (data.vertexPartition u).Rel s t ↔
      s = t ∨ ((s = ℓ₁ ∨ s = ℓ₂) ∧ (t = ℓ₁ ∨ t = ℓ₂)) := by
  classical
  obtain ⟨huw, hvw, huv'⟩ := side_of_huv hab Hl.huv
  obtain ⟨F, hF, hFu⟩ := exists_fold fd H Hl
  -- `|F| = 2`
  have hF2 : size data F = 2 := by
    have hr2 : 2 ≤ ram data F :=
      NonTrivalentValencyTwoRigidity.two_le_localRamification_of_target_leaf data
        fd.connected F (by rw [hFu]; exact Hl.u1) ((mem_fib_iff data hc hab hOne block F).mp hF).2.2
    have hr := ram_le_targetChange data fd F
    rw [hFu, Hl.chu] at hr
    have hN := NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data F
    have hu1 : (GluingDatum.incidentEdges F.1.1).card = 1 := by rw [hFu]; exact Hl.u1
    rw [hu1] at hN
    have hN' : (Fintype.card (IncidentSourceEdge data F) : ℤ) =
        ram data F + 2 - size data F := by rw [hN]; unfold ram size; push_cast; ring
    have hLe := StableLocalProperties.card_incidentSourceEdge_le_blockCard_of_target_leaf data F hu1
    have hnd := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data F
    have hnd2 := ValencyThreeSplit.nonDanglingValency_two_le data fd
      ((mem_fib_iff data hc hab hOne block F).mp hF).2.2
    have : (2 : ℤ) ≤ Fintype.card (IncidentSourceEdge data F) := by exact_mod_cast hnd2.trans hnd
    have hsz : (size data F : ℤ) = ((data.vertexPartition F.1.1).blockCard F.1.2 : ℤ) := rfl
    omega
  have hF2' : ((data.vertexPartition F.1.1).block F.1.2).card = 2 := hF2
  obtain ⟨ℓ₁, ℓ₂, h12, hblk⟩ := Finset.card_eq_two.mp hF2'
  have hmem : ∀ z, z ∈ (data.vertexPartition F.1.1).block F.1.2 ↔ z = ℓ₁ ∨ z = ℓ₂ := by
    intro z; rw [hblk]; simp
  have hFrel : ∀ z, (data.vertexPartition u).Rel F.1.2 z ↔ z = ℓ₁ ∨ z = ℓ₂ := by
    intro z; rw [← hmem, SheetPartition.mem_block_iff, hFu]
  have hFA : (mergedPartition data a b).Rel block.1 F.1.2 := by
    obtain ⟨-, hrepr, -⟩ := (mem_fib_iff data hc hab hOne block F).mp hF
    change (mergedPartition data a b).repr block.1 = (mergedPartition data a b).repr F.1.2
    rw [block.2]; exact hrepr.symm
  have href : (data.vertexPartition u).Refines (mergedPartition data a b) :=
    ValencyThreeResolutionMatch.refines_merged_u data Hl.huv
  have hA : ∀ z, (z = ℓ₁ ∨ z = ℓ₂) → (mergedPartition data a b).Rel block.1 z :=
    fun z hz ↦ hFA.trans (href.rel ((hFrel z).mpr hz))
  refine ⟨ℓ₁, ℓ₂, h12, hA ℓ₁ (Or.inl rfl), hA ℓ₂ (Or.inr rfl), ?_, fun s t ↦ ?_⟩
  · -- the two sheets of the fold lie over two different constituents over `v`
    intro hv
    obtain ⟨t₀, ht₀, ht₀c⟩ : ∃ t₀ ∈ GluingDatum.incidentEdges v, t₀ ≠ contracted := by
      have : 1 < (GluingDatum.incidentEdges v).card := by rw [Hl.v3]; norm_num
      exact Finset.exists_mem_ne this contracted
    have hY := endpoint_mem_fib fd H hvw ht₀ ht₀c (hA ℓ₁ (Or.inl rfl))
    have hcu := contracted_mem_incidentEdges hc huw
    have hcv := contracted_mem_incidentEdges hc hvw
    have hFℓ : ∀ z, (z = ℓ₁ ∨ z = ℓ₂) → data.sourceEndpoint u z = F := by
      intro z hz
      exact (data.sourceEndpoint_eq_iff _ _ _).mpr ⟨hFu.symm, ((hFrel z).mpr hz).symm⟩
    have h1 := incident_sourceEdge_sourceEndpoint data u contracted hcu ℓ₁
    have h2 := incident_sourceEdge_sourceEndpoint data v contracted hcv ℓ₁
    have h3 := incident_sourceEdge_sourceEndpoint data u contracted hcu ℓ₂
    have h4 := incident_sourceEdge_sourceEndpoint data v contracted hcv ℓ₂
    rw [hFℓ ℓ₁ (Or.inl rfl)] at h1
    rw [hFℓ ℓ₂ (Or.inr rfl)] at h3
    rw [sourceEndpoint_eq_of_rel hv] at h4
    have hFY : F ≠ data.sourceEndpoint v ℓ₁ := fun h ↦
      huv' (hFu.symm.trans (congrArg (fun X : data.SourceVertex ↦ X.1.1) h))
    have hEq := eq_of_same_ends data hc hab hOne block H.forest hF hY hFY h1 h2 h3 h4
    have hrel : (data.edgePartition contracted).Rel ℓ₁ ℓ₂ :=
      congrArg (fun e : data.SourceEdge ↦ e.1.2) hEq
    exact h12 ((contracted_rel_leaf fd H Hl ℓ₁ ℓ₂).mp hrel)
  · constructor
    · intro hst
      by_cases hsF : s = ℓ₁ ∨ s = ℓ₂
      · right
        refine ⟨hsF, (hFrel t).mp (((hFrel s).mpr hsF).trans hst)⟩
      · left
        have hXF : data.sourceEndpoint u s ≠ F := by
          intro h
          apply hsF
          have := ((data.sourceEndpoint_eq_iff _ _ _).mp h).2
          exact (hFrel s).mp this.symm
        have h1 := size_one_of_ne_fold fd Hl hF hFu rfl hXF
        change (data.vertexPartition u).blockCard ((data.vertexPartition u).repr s) = 1 at h1
        have hr1 := eq_of_blockCard_one h1 ((data.vertexPartition u).rel_repr_left s)
        have hr2 := eq_of_blockCard_one h1 (((data.vertexPartition u).rel_repr_left s).trans hst)
        exact hr1.symm.trans hr2
    · rintro (rfl | ⟨hs, ht⟩)
      · rfl
      · exact ((hFrel s).mpr hs).symm.trans ((hFrel t).mpr ht)

include fd H Hl in
/-- **The trivalent endpoint's partition**: the merged partition off the anchor, and on the
anchor one class of each non-contracted occurrence there (`Y`, `Z`). -/
theorem tri_rel {t₀ : target.edges} (ht₀ : t₀ ∈ GluingDatum.incidentEdges v)
    (ht₀c : t₀ ≠ contracted) (s t : Fin degree) :
    (data.vertexPartition v).Rel s t ↔ (mergedPartition data a b).Rel s t ∧
      ((mergedPartition data a b).Rel block.1 s → (data.edgePartition t₀).Rel s t) := by
  classical
  obtain ⟨huw, hvw, -⟩ := side_of_huv hab Hl.huv
  have href : (data.vertexPartition v).Refines (mergedPartition data a b) :=
    ValencyThreeResolutionMatch.refines_merged_v data Hl.huv
  have hEref := edgePartition_refines_of_mem_incidentEdges data v t₀ ht₀
  by_cases hs : (mergedPartition data a b).Rel block.1 s
  · constructor
    · intro hst
      refine ⟨href.rel hst, fun _ ↦ ?_⟩
      have hX := endpoint_mem_fib fd H hvw ht₀ ht₀c hs
      have hr0 : ram data (data.sourceEndpoint v s) = 0 :=
        W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd _ Hl.chv
      have hf := incident_sourceEdge_sourceEndpoint data v t₀ ht₀ s
      have hg := incident_sourceEdge_sourceEndpoint data v t₀ ht₀ t
      rw [sourceEndpoint_eq_of_rel hst] at hg
      have hmap := sourceVertexMap_endpoint (hc := hc) (hab := hab) (hOne := hOne) hvw hs
      have hfd := survive fd H hmap hf ht₀c
      have hgd := survive fd H hmap hg ht₀c
      have hEq := ValencyThreeSplit.eq_of_ram_zero data fd hr0 ((mem_ndAt data _ _).mpr ⟨hfd, hf⟩)
        ((mem_ndAt data _ _).mpr ⟨hgd, hg⟩) rfl
      exact congrArg (fun e : data.SourceEdge ↦ e.1.2) hEq
    · rintro ⟨-, h⟩; exact hEref.rel (h hs)
  · have hv := pv_eq_merged data hc hab Hl.forest Hl.huv s (fun x hx z _ hxz ↦ ?_) t
    · rw [hv]; exact ⟨fun h ↦ ⟨h, fun h' ↦ absurd h' hs⟩, fun h ↦ h.1⟩
    · -- off the anchor the leaf side is discrete
      obtain ⟨F, hF, hFu⟩ := exists_fold fd H Hl
      have hxA : ¬ (mergedPartition data a b).Rel block.1 x := by
        intro h
        rw [SheetPartition.mem_block_iff] at hx
        exact hs (h.trans hx.symm)
      have hXF : data.sourceEndpoint u x ≠ F := by
        intro h
        apply hxA
        obtain ⟨-, hrepr, -⟩ := (mem_fib_iff data hc hab hOne block F).mp hF
        have h1 := ((data.sourceEndpoint_eq_iff _ _ _).mp h).2
        rw [← hFu] at h1
        have href' : (data.vertexPartition u).Refines (mergedPartition data a b) :=
          ValencyThreeResolutionMatch.refines_merged_u data Hl.huv
        rw [← hFu] at href'
        change (mergedPartition data a b).repr block.1 = (mergedPartition data a b).repr x
        rw [block.2, ← hrepr]
        exact (href'.rel h1).symm
      have h1 := size_one_of_ne_fold fd Hl hF hFu rfl hXF
      change (data.vertexPartition u).blockCard ((data.vertexPartition u).repr x) = 1 at h1
      have hr1 := eq_of_blockCard_one h1 ((data.vertexPartition u).rel_repr_left x)
      have hr2 := eq_of_blockCard_one h1 (((data.vertexPartition u).rel_repr_left x).trans hxz)
      rw [← hr1.symm.trans hr2]
      exact rfl

include fd Hl in
/-- **Paired survivors at a leaf split span the same sheets**: both are a whole trivalent
constituent (index = size). -/
theorem paired_rel_iff {i j : Fin 4} (hP : Paired L i j) (s : Fin degree) :
    (data.edgePartition (lift L i).1.1).Rel (lift L i).1.2 s ↔
      (data.edgePartition (lift L j).1.1).Rel (lift L j).1.2 s := by
  obtain ⟨X, hX, Y, hY, hi, hj, hXY⟩ := hP
  have hbi : lift L i ∈ bdAt data contracted X := (mem_bdAt data _ _).mpr ⟨hi, lift_ne L i⟩
  have hbj : lift L j ∈ bdAt data contracted Y := (mem_bdAt data _ _).mpr ⟨hj, lift_ne L j⟩
  have hEq := LeafInput.eq_of_pairedE (Hl.home fd hX hbi).1 (Hl.home fd hY hbj).1 hXY
  subst hEq
  have hIi := rel_iff_of_index data ((mem_ndAt data _ _).mp hi).2 (by
    have := Hl.index_eq fd hX hbi; exact_mod_cast this) s
  have hIj := rel_iff_of_index data ((mem_ndAt data _ _).mp hj).2 (by
    have := Hl.index_eq fd hX hbj; exact_mod_cast this) s
  rw [hIi, hIj]

end Leaf

/-! ## 5.  The two transports, in limit coordinates -/

section AbstractTransport

open ResolutionExpansionFree
open ResolutionM11 (LocalResolution)
open ValencyThreeResolutionMatch (anchor_iff ends_of_mem mem_of_ends)
open W3Nd2StarExhaustionProof (edge_rel_iff edgePerm_agree agree_symm_apply incident_iff)

variable {T₁ T₂ : CFGraph} {d : ℕ} {D₁ : GluingDatum T₁ d} {D₂ : GluingDatum T₂ d}
  (ψ : GeometricDatumIso D₁ D₂) {W₁ : T₁.V} {W₂ : T₂.V} (hWall : ψ.targetVertex W₁ = W₂)

include hWall in
/-- **The transport at a `(2,2)` split.**  The retained side uses the left direction's
permutation, the fresh side the right direction's, and the regrown occurrence the left one
corrected inside `A_l` so that the right pass-through class goes to the right pass-through
class.  Everything is read in limit coordinates: each endpoint partition is the merged
partition off the anchor and, on the anchor, its direction's partition with the non-pass
classes merged (`NP`); the regrown occurrence is their common refinement. -/
theorem transport_div (Dl Dr : T₁.edges) (hW : ∀ e, e ∈ GluingDatum.incidentEdges W₁ ↔ e = Dl ∨ e = Dr)
    (r₁ : T₁.edges → Bool) (r₂ : T₂.edges → Bool) (hr₁l : r₁ Dl = false) (hr₁r : r₁ Dr = true)
    (hside : ∀ e, r₂ (ψ.targetEdge e) = r₁ e)
    (block₁ block₂ : Fin d)
    (hA : (D₂.vertexPartition W₂).Rel block₂ (ψ.vertexPerm W₁ block₁))
    (NPl₁ NPr₁ NPl₂ NPr₂ : Fin d → Prop) (res₁ res₂ : LocalResolution d)
    (h1l : ∀ s t, res₁.left.Rel s t ↔ (D₁.vertexPartition W₁).Rel s t ∧
      ((D₁.vertexPartition W₁).Rel block₁ s → (D₁.edgePartition Dl).Rel s t ∨ (NPl₁ s ∧ NPl₁ t)))
    (h1r : ∀ s t, res₁.right.Rel s t ↔ (D₁.vertexPartition W₁).Rel s t ∧
      ((D₁.vertexPartition W₁).Rel block₁ s → (D₁.edgePartition Dr).Rel s t ∨ (NPr₁ s ∧ NPr₁ t)))
    (h1n : ∀ s t, res₁.newEdge.Rel s t ↔ res₁.left.Rel s t ∧ res₁.right.Rel s t)
    (h1or : ∀ s, (D₁.vertexPartition W₁).Rel block₁ s → NPl₁ s ∨ NPr₁ s)
    (h2l : ∀ s t, res₂.left.Rel s t ↔ (D₂.vertexPartition W₂).Rel s t ∧
      ((D₂.vertexPartition W₂).Rel block₂ s →
        (D₂.edgePartition (ψ.targetEdge Dl)).Rel s t ∨ (NPl₂ s ∧ NPl₂ t)))
    (h2r : ∀ s t, res₂.right.Rel s t ↔ (D₂.vertexPartition W₂).Rel s t ∧
      ((D₂.vertexPartition W₂).Rel block₂ s →
        (D₂.edgePartition (ψ.targetEdge Dr)).Rel s t ∨ (NPr₂ s ∧ NPr₂ t)))
    (h2n : ∀ s t, res₂.newEdge.Rel s t ↔ res₂.left.Rel s t ∧ res₂.right.Rel s t)
    (h2or : ∀ s, (D₂.vertexPartition W₂).Rel block₂ s → NPl₂ s ∨ NPr₂ s)
    (h2pass : ∀ x y, (D₂.vertexPartition W₂).Rel block₂ x → ¬ NPr₂ x →
      (D₂.vertexPartition W₂).Rel block₂ y → ¬ NPr₂ y →
        (D₂.edgePartition (ψ.targetEdge Dr)).Rel x y)
    (hNPl : ∀ s, NPl₁ s ↔ NPl₂ (ψ.edgePerm Dl s)) (hNPr : ∀ s, NPr₁ s ↔ NPr₂ (ψ.edgePerm Dr s)) :
    Nonempty (TransportFree ψ W₁ W₂ r₁ r₂ res₁ res₂) := by
  classical
  set M₁ := D₁.vertexPartition W₁
  set M₂ := D₂.vertexPartition W₂
  set σl := ψ.edgePerm Dl
  set σr := ψ.edgePerm Dr
  have hDl : ψ.targetEdge Dl ∈ GluingDatum.incidentEdges W₂ :=
    (incident_iff ψ hWall Dl).mp (ends_of_mem ((hW Dl).mpr (Or.inl rfl)))
  have hDr : ψ.targetEdge Dr ∈ GluingDatum.incidentEdges W₂ :=
    (incident_iff ψ hWall Dr).mp (ends_of_mem ((hW Dr).mpr (Or.inr rfl)))
  have hσl := edgePerm_agree ψ hWall Dl hDl
  have hσr := edgePerm_agree ψ hWall Dr hDr
  have hMl := M11StarExhaustionProof.wall_rel_iff_of_agree ψ hWall σl hσl
  have hMr := M11StarExhaustionProof.wall_rel_iff_of_agree ψ hWall σr hσr
  have hAl := anchor_iff ψ hWall block₁ block₂ hA σl hσl
  have hAr := anchor_iff ψ hWall block₁ block₂ hA σr hσr
  -- the two endpoint partitions are carried by their directions' permutations
  have hL : ∀ x y, res₁.left.Rel x y ↔ res₂.left.Rel (σl x) (σl y) := by
    intro x y
    rw [h1l, h2l, hMl, hAl, edge_rel_iff ψ Dl, hNPl, hNPl]
  have hR : ∀ x y, res₁.right.Rel x y ↔ res₂.right.Rel (σr x) (σr y) := by
    intro x y
    rw [h1r, h2r, hMr, hAr, edge_rel_iff ψ Dr, hNPr, hNPr]
  -- the regrown occurrence: move the right pass-through class inside `A_l`
  set P₀ := Finset.univ.filter fun s ↦ M₁.Rel block₁ s ∧ ¬ NPr₁ s
  set P := P₀.image σl
  set Q := Finset.univ.filter fun x ↦ M₂.Rel block₂ x ∧ ¬ NPr₂ x
  have hQ : Q = P₀.image σr := by
    ext x
    simp only [Q, P₀, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hx, hnx⟩
      refine ⟨σr.symm x, ⟨?_, ?_⟩, σr.apply_symm_apply x⟩
      · rw [hAr, σr.apply_symm_apply]; exact hx
      · rw [hNPr, σr.apply_symm_apply]; exact hnx
    · rintro ⟨s, ⟨hs, hns⟩, rfl⟩
      exact ⟨(hAr s).mp hs, (hNPr s).not.mp hns⟩
  have hcard : P.card = Q.card := by
    rw [hQ, Finset.card_image_of_injective _ σl.injective,
      Finset.card_image_of_injective _ σr.injective]
  obtain ⟨g, hg1, hg2, hg3⟩ := ValencyThreeResolutionMatch.exists_perm_image
    (fun x ↦ M₂.Rel block₂ x ∧ NPl₂ x) P Q
    (by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hsA, hsn⟩ := (Finset.mem_filter.mp hs).2
      exact ⟨(hAl s).mp hsA, (hNPl s).mp ((h1or s hsA).resolve_right hsn)⟩)
    (by
      intro x hx
      obtain ⟨hxA, hxn⟩ := (Finset.mem_filter.mp hx).2
      exact ⟨hxA, (h2or x hxA).resolve_right hxn⟩)
    hcard
  set τN : Equiv.Perm (Fin d) := σl.trans g
  have hτN : ∀ s, τN s = g (σl s) := fun _ ↦ rfl
  have hgA : ∀ x, M₂.Rel block₂ x → M₂.Rel block₂ (g x) := by
    intro x hx
    by_cases hD : M₂.Rel block₂ x ∧ NPl₂ x
    · exact (hg2 x hD).1
    · rw [hg1 x hD]; exact hx
  -- the regrown permutation agrees with both endpoint permutations
  have hNl : ∀ s, res₂.left.Rel (τN s) (σl s) := by
    intro s
    rw [hτN]
    by_cases hD : M₂.Rel block₂ (σl s) ∧ NPl₂ (σl s)
    · have hD' := hg2 _ hD
      rw [h2l]
      exact ⟨hD'.1.symm.trans hD.1, fun _ ↦ Or.inr ⟨hD'.2, hD.2⟩⟩
    · rw [hg1 _ hD]
      exact (res₂.left.rel_repr_left _).symm.trans (res₂.left.rel_repr_left _)
  have hNr : ∀ s, res₂.right.Rel (τN s) (σr s) := by
    intro s
    rw [hτN]
    have hM : M₂.Rel (σl s) (σr s) := by
      have := (hMr (σr.symm (σl s)) s).mp (agree_symm_apply ψ σr σl hσr hσl s)
      rwa [σr.apply_symm_apply] at this
    by_cases hsA : M₁.Rel block₁ s
    · have hlA := (hAl s).mp hsA
      have hrA := (hAr s).mp hsA
      have hgM : M₂.Rel (g (σl s)) (σr s) := (hgA _ hlA).symm.trans hrA
      rw [h2r]
      refine ⟨hgM, fun _ ↦ ?_⟩
      by_cases hns : NPr₁ s
      · -- `σl s` is not moved into `Q`
        right
        refine ⟨?_, (hNPr s).mp hns⟩
        by_contra hn
        have hgQ : g (σl s) ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgA _ hlA, hn⟩
        rw [hg3] at hgQ
        obtain ⟨s', hs', hss'⟩ := Finset.mem_image.mp hgQ
        rw [σl.injective hss'] at hs'
        exact (Finset.mem_filter.mp hs').2.2 hns
      · -- `s` is in the right pass-through class
        left
        have hsP : σl s ∈ P :=
          Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsA, hns⟩, rfl⟩
        have hgQ := (hg3 _).mpr hsP
        obtain ⟨hgA', hgn⟩ := (Finset.mem_filter.mp hgQ).2
        exact h2pass _ _ hgA' hgn hrA ((hNPr s).not.mp hns)
    · have hnA : ¬ M₂.Rel block₂ (σl s) := fun h ↦ hsA ((hAl s).mpr h)
      rw [hg1 _ (fun h ↦ hnA h.1), h2r]
      exact ⟨hM, fun h ↦ absurd h hnA⟩
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel ψ W₁ W₂ r₁ r₂ res₁ res₂ hWall hside
    (fun x y h ↦ ((h1l x y).mp h).1) (fun x y h ↦ ((h1r x y).mp h).1) σl σr τN hσl hσr hL hR
    ?_ ?_ ?_ ?_
  · intro x y
    rw [h1n, h2n, hL, hR]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hNl x).trans (h1.trans (hNl y).symm), (hNr x).trans (h2.trans (hNr y).symm)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hNl x).symm.trans (h1.trans (hNl y)), (hNr x).symm.trans (h2.trans (hNr y))⟩
  · intro s
    rw [hL, σl.apply_symm_apply]; exact hNl s
  · intro s
    rw [hR, σr.apply_symm_apply]; exact hNr s
  · intro edge hInc s
    rcases (hW edge).mp (mem_of_ends hInc) with rfl | rfl
    · rw [hr₁l]; simp only [Bool.false_eq_true, ite_false, σl, Equiv.symm_apply_apply]
      exact rfl
    · rw [hr₁r]; simp only [ite_true, σr, Equiv.symm_apply_apply]
      exact rfl

/-- A swap of two related sheets preserves every class. -/
theorem swap_rel {P : SheetPartition d} {p q : Fin d} (h : P.Rel p q) (x : Fin d) :
    P.Rel (Equiv.swap p q x) x := by
  rcases eq_or_ne x p with rfl | hxp
  · rw [Equiv.swap_apply_left]; exact h.symm
  rcases eq_or_ne x q with rfl | hxq
  · rw [Equiv.swap_apply_right]; exact h
  rw [Equiv.swap_apply_of_ne_of_ne hxp hxq]
  exact rfl

include hWall in
/-- **The transport at a leaf split.**  The trivalent side uses one direction's permutation;
the leaf side, and the regrown occurrence (discrete on both covers), use it corrected inside
the two trivalent constituents by two swaps, so that the fold's two sheets go to the fold's two
sheets.  The other direction is compatible because the two covers pair the survivors in the
same way (`hcross`). -/
theorem transport_leaf (Dt D₃ : T₁.edges)
    (hW : ∀ e, e ∈ GluingDatum.incidentEdges W₁ ↔ e = Dt ∨ e = D₃)
    (r₁ : T₁.edges → Bool) (r₂ : T₂.edges → Bool)
    (hr₁ : ∀ e, e ∈ GluingDatum.incidentEdges W₁ → r₁ e = true)
    (hside : ∀ e, r₂ (ψ.targetEdge e) = r₁ e)
    (block₁ block₂ : Fin d)
    (hA : (D₂.vertexPartition W₂).Rel block₂ (ψ.vertexPerm W₁ block₁))
    (ℓ₁ ℓ₂ ℓ₁' ℓ₂' : Fin d) (h12' : ℓ₁' ≠ ℓ₂') (res₁ res₂ : LocalResolution d)
    (h1l : ∀ s t, res₁.left.Rel s t ↔ s = t ∨ ((s = ℓ₁ ∨ s = ℓ₂) ∧ (t = ℓ₁ ∨ t = ℓ₂)))
    (h1r : ∀ s t, res₁.right.Rel s t ↔ (D₁.vertexPartition W₁).Rel s t ∧
      ((D₁.vertexPartition W₁).Rel block₁ s → (D₁.edgePartition Dt).Rel s t))
    (h1n : ∀ s t, res₁.newEdge.Rel s t ↔ s = t)
    (hℓ₁ : (D₁.vertexPartition W₁).Rel block₁ ℓ₁) (hℓ₂ : (D₁.vertexPartition W₁).Rel block₁ ℓ₂)
    (hℓ : ¬ res₁.right.Rel ℓ₁ ℓ₂)
    (h2l : ∀ s t, res₂.left.Rel s t ↔ s = t ∨ ((s = ℓ₁' ∨ s = ℓ₂') ∧ (t = ℓ₁' ∨ t = ℓ₂')))
    (h2r : ∀ s t, res₂.right.Rel s t ↔ (D₂.vertexPartition W₂).Rel s t ∧
      ((D₂.vertexPartition W₂).Rel block₂ s → (D₂.edgePartition (ψ.targetEdge Dt)).Rel s t))
    (h2n : ∀ s t, res₂.newEdge.Rel s t ↔ s = t)
    (h2cover : ∀ x, (D₂.vertexPartition W₂).Rel block₂ x →
      res₂.right.Rel ℓ₁' x ∨ res₂.right.Rel ℓ₂' x)
    (hcross : ∀ s, (D₁.vertexPartition W₁).Rel block₁ s →
      (D₂.edgePartition (ψ.targetEdge Dt)).Rel (ψ.edgePerm D₃ s) (ψ.edgePerm Dt s)) :
    Nonempty (TransportFree ψ W₁ W₂ r₁ r₂ res₁ res₂) := by
  classical
  set M₁ := D₁.vertexPartition W₁
  set M₂ := D₂.vertexPartition W₂
  set σ := ψ.edgePerm Dt
  set σ₃ := ψ.edgePerm D₃
  have hDt : ψ.targetEdge Dt ∈ GluingDatum.incidentEdges W₂ :=
    (incident_iff ψ hWall Dt).mp (ends_of_mem ((hW Dt).mpr (Or.inl rfl)))
  have hD₃ : ψ.targetEdge D₃ ∈ GluingDatum.incidentEdges W₂ :=
    (incident_iff ψ hWall D₃).mp (ends_of_mem ((hW D₃).mpr (Or.inr rfl)))
  have hσ := edgePerm_agree ψ hWall Dt hDt
  have hσ₃ := edgePerm_agree ψ hWall D₃ hD₃
  have hMσ := M11StarExhaustionProof.wall_rel_iff_of_agree ψ hWall σ hσ
  have hAσ := anchor_iff ψ hWall block₁ block₂ hA σ hσ
  have hA₃ := anchor_iff ψ hWall block₁ block₂ hA σ₃ hσ₃
  have hR : ∀ x y, res₁.right.Rel x y ↔ res₂.right.Rel (σ x) (σ y) := by
    intro x y
    rw [h1r, h2r, hMσ, hAσ, edge_rel_iff ψ Dt]
  have hR2 : ∀ x y, res₂.right.Rel x y → M₂.Rel x y := fun x y h ↦ ((h2r x y).mp h).1
  have hσℓ : ¬ res₂.right.Rel (σ ℓ₁) (σ ℓ₂) := fun h ↦ hℓ ((hR _ _).mpr h)
  -- the matching of the two folds
  have key : ∀ m₁ m₂ : Fin d, ((m₁ = ℓ₁' ∧ m₂ = ℓ₂') ∨ (m₁ = ℓ₂' ∧ m₂ = ℓ₁')) →
      res₂.right.Rel m₁ (σ ℓ₁) → res₂.right.Rel m₂ (σ ℓ₂) →
      Nonempty (TransportFree ψ W₁ W₂ r₁ r₂ res₁ res₂) := by
    intro m₁ m₂ hm hm₁ hm₂
    have hm12 : m₁ ≠ m₂ := by rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact h12'; exact h12'.symm]
    have hm₂σ₁ : m₂ ≠ σ ℓ₁ := fun h ↦ hσℓ (h ▸ hm₂)
    have hσ₁σ₂ : σ ℓ₁ ≠ σ ℓ₂ := fun h ↦ hσℓ (h ▸ rfl)
    set π : Equiv.Perm (Fin d) := Equiv.swap (σ ℓ₂) m₂ |>.trans (Equiv.swap (σ ℓ₁) m₁)
    have hπ : ∀ x, π x = Equiv.swap (σ ℓ₁) m₁ (Equiv.swap (σ ℓ₂) m₂ x) := fun _ ↦ rfl
    have hπR : ∀ x, res₂.right.Rel (π x) x := fun x ↦ by
      rw [hπ]
      exact (swap_rel hm₁.symm _).trans (swap_rel hm₂.symm x)
    have hπ₁ : π (σ ℓ₁) = m₁ := by
      rw [hπ, Equiv.swap_apply_of_ne_of_ne hσ₁σ₂ hm₂σ₁.symm, Equiv.swap_apply_left]
    have hπ₂ : π (σ ℓ₂) = m₂ := by
      rw [hπ, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hm₂σ₁ hm12.symm]
    set τ : Equiv.Perm (Fin d) := σ.trans π
    have hτ : ∀ x, τ x = π (σ x) := fun _ ↦ rfl
    have hmem : ∀ x, (x = ℓ₁ ∨ x = ℓ₂) ↔ (τ x = ℓ₁' ∨ τ x = ℓ₂') := by
      intro x
      have hτ₁ : τ ℓ₁ = m₁ := hπ₁
      have hτ₂ : τ ℓ₂ = m₂ := hπ₂
      constructor
      · rintro (rfl | rfl) <;> rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
      · intro h
        have h' : τ x = τ ℓ₁ ∨ τ x = τ ℓ₂ := by
          rw [hτ₁, hτ₂]; rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
        rcases h' with h' | h'
        · exact Or.inl (τ.injective h')
        · exact Or.inr (τ.injective h')
    have hτm : ∀ s, M₁.Rel ((ψ.vertexPerm W₁).symm (τ s)) s := by
      intro s
      have h1 : M₂.Rel (π (σ s)) (σ s) := hR2 _ _ (hπR _)
      have h2 := (M11StarExhaustionProof.wall_rel_iff ψ hWall _ _).mp h1
      exact h2.trans (hσ s)
    refine M11StarExhaustionProof.nonempty_transportFree_of_rel ψ W₁ W₂ r₁ r₂ res₁ res₂ hWall hside
      ?_ (fun x y h ↦ ((h1r x y).mp h).1) τ σ τ hτm hσ ?_ hR ?_ ?_ ?_ ?_
    · intro x y h
      rcases (h1l x y).mp h with rfl | ⟨hx, hy⟩
      · rfl
      · have hx' : M₁.Rel block₁ x := by rcases hx with rfl | rfl <;> assumption
        have hy' : M₁.Rel block₁ y := by rcases hy with rfl | rfl <;> assumption
        exact hx'.symm.trans hy'
    · intro x y
      rw [h1l, h2l, hmem x, hmem y, τ.injective.eq_iff]
    · intro x y
      rw [h1n, h2n, τ.injective.eq_iff]
    · intro s
      rw [Equiv.symm_apply_apply]
      exact rfl
    · intro s
      rw [hR, Equiv.apply_symm_apply, hτ]
      exact hπR _
    · intro edge hInc s
      have hmemW := mem_of_ends hInc
      rw [hr₁ edge hmemW]
      simp only [ite_true]
      rcases (hW edge).mp hmemW with rfl | rfl
      · rw [Equiv.symm_apply_apply]; exact rfl
      · rw [hR, Equiv.apply_symm_apply, h2r]
        refine ⟨?_, fun h ↦ hcross s ((hA₃ s).mpr h)⟩
        have := (hMσ (σ.symm (σ₃ s)) s).mp (agree_symm_apply ψ σ σ₃ hσ hσ₃ s)
        rwa [σ.apply_symm_apply] at this
  -- choose the matching
  have hℓ₁A := (hAσ ℓ₁).mp hℓ₁
  have hℓ₂A := (hAσ ℓ₂).mp hℓ₂
  by_cases h1 : res₂.right.Rel ℓ₁' (σ ℓ₁)
  · have h2 : res₂.right.Rel ℓ₂' (σ ℓ₂) := by
      rcases h2cover _ hℓ₂A with h | h
      · exact absurd (h1.symm.trans h) hσℓ
      · exact h
    exact key ℓ₁' ℓ₂' (Or.inl ⟨rfl, rfl⟩) h1 h2
  · have h1' : res₂.right.Rel ℓ₂' (σ ℓ₁) := (h2cover _ hℓ₁A).resolve_left h1
    have h2 : res₂.right.Rel ℓ₁' (σ ℓ₂) := by
      rcases h2cover _ hℓ₂A with h | h
      · exact h
      · exact absurd (h1'.symm.trans h) hσℓ
    exact key ℓ₂' ℓ₁' (Or.inr ⟨rfl, rfl⟩) h1' h2

end AbstractTransport

/-! ## 6.  The placements and the incoming resolution, in limit coordinates -/

section Wall

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The placement disjunction of `M11WallExhaustion.incomingResolution`. -/
abbrev Placed (sec : (contract target hab hOne).edges → Bool) : Prop :=
  (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = sec edge) ∨
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = !(sec edge))

include fd in
/-- **The incoming resolution at a placement**: the regrown occurrence is the contracted
occurrence's partition, and the two endpoint partitions are `a`'s and `b`'s, in the order the
placement dictates. -/
theorem resolution_eq (sec : (contract target hab hOne).edges → Bool) (hP : Placed hc hab hOne sec) :
    (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).newEdge =
        data.edgePartition contracted ∧
      ((∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
          IncomingTargetExpansion.right hc hab hOne e = sec e) →
        (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).left =
            data.vertexPartition a ∧
          (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right =
            data.vertexPartition b) ∧
      (¬ (∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
          IncomingTargetExpansion.right hc hab hOne e = sec e) →
        (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).left =
            data.vertexPartition b ∧
          (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right =
            data.vertexPartition a) := by
  have hpair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne sec hP
  have hnew := M11IncomingOuterPartitions.transported_edgePartition_new data hc hab hOne sec hP
    fd.targetConnected fd.targetGenus
  refine ⟨hnew, fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [ite_eq_left h] at hpair
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  · rw [ite_eq_right h] at hpair
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- The side of a folded occurrence. -/
theorem right_foldEdge {t : target.edges} (htc : t ≠ contracted) :
    IncomingTargetExpansion.right hc hab hOne (foldEdge hc hab hOne ⟨t, htc⟩) =
      decide ((t : target.V × target.V).1 = b ∨ (t : target.V × target.V).2 = b) := by
  unfold IncomingTargetExpansion.right
  rw [unfoldEdge_foldEdge]

theorem right_foldEdge_a {t : target.edges} (ht : t ∈ GluingDatum.incidentEdges a)
    (htc : t ≠ contracted) :
    IncomingTargetExpansion.right hc hab hOne (foldEdge hc hab hOne ⟨t, htc⟩) = false := by
  rw [right_foldEdge]
  refine decide_eq_false fun h ↦ ?_
  exact ValencyThreeSplit.not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) ht htc
    ((mem_incidentEdges_iff b t).mpr h)

theorem right_foldEdge_b {t : target.edges} (ht : t ∈ GluingDatum.incidentEdges b)
    (htc : t ≠ contracted) :
    IncomingTargetExpansion.right hc hab hOne (foldEdge hc hab hOne ⟨t, htc⟩) = true := by
  rw [right_foldEdge]
  exact decide_eq_true ((mem_incidentEdges_iff b t).mp ht)

theorem foldEdge_mem_wall {t : target.edges} (htc : t ≠ contracted)
    (ht : t ∈ GluingDatum.incidentEdges a ∨ t ∈ GluingDatum.incidentEdges b) :
    foldEdge hc hab hOne ⟨t, htc⟩ ∈
      GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
  foldEdge_mem_incidentEdges_merge hc hab hOne htc (Finset.mem_union.mpr ht)

theorem eq_foldEdge_unfold (e : (contract target hab hOne).edges) :
    e = foldEdge hc hab hOne ⟨unfoldEdge hc hab hOne e, unfoldEdge_ne_contracted hc hab hOne e⟩ :=
  ((foldEdgeEquiv hc hab hOne).apply_symm_apply e).symm

/-- **The limit partition of a wall occurrence is the incoming partition of its unfolding.** -/
theorem limit_edgePartition (e : (contract target hab hOne).edges) :
    (contractDatum data hc hab hOne).edgePartition e = data.edgePartition (unfoldEdge hc hab hOne e) :=
  contractDatum_edgePartition data hc hab hOne e

end Wall

/-! ## 7.  The `(2,2)` package: the hypotheses of `transport_div` read off one cover -/

section DivPackage

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (H : AnchorInput data hc hab hOne block)
  (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- The non-pass survivors over a wall occurrence, as a sheet predicate in limit
coordinates. -/
def NPlim (D : (contract target hab hOne).edges) (s : Fin degree) : Prop :=
  ∃ i, (L.e i).1.1 = D ∧ ¬ PassAt L i ∧
    ((contractDatum data hc hab hOne).edgePartition D).Rel (L.e i).1.2 s

theorem label_sheet (i : Fin 4) : (L.e i).1.2 = (lift L i).1.2 := by
  rw [← ValencyTwoSplit.sourceEdgeMap_lift L i]
  rfl

theorem label_unfold (i : Fin 4) : unfoldEdge hc hab hOne (L.e i).1.1 = (lift L i).1.1 := by
  rw [← ValencyTwoSplit.sourceEdgeMap_lift L i]
  exact unfoldEdge_foldEdge hc hab hOne ⟨_, lift_ne L i⟩

theorem unfoldEdge_injective : Function.Injective (unfoldEdge hc hab hOne) := by
  intro e f h
  exact (foldEdgeEquiv hc hab hOne).symm.injective (Subtype.ext h)

theorem np_iff_nplim (D : (contract target hab hOne).edges) (s : Fin degree) :
    NP L (unfoldEdge hc hab hOne D) s ↔ NPlim L D s := by
  unfold NP NPlim
  refine exists_congr fun i ↦ ?_
  rw [← label_unfold L i, ← label_sheet L i, limit_edgePartition hc hab hOne D,
    (unfoldEdge_injective (hc := hc) (hab := hab) (hOne := hOne)).eq_iff]

variable (Hd : DivInput data hc hab hOne block)

include fd H Hd in
/-- **The endpoint partition at a `(2,2)` split, on every merged class.** -/
theorem side_rel {x : target.V} (hx : x = a ∨ x = b) {t₀ : target.edges}
    (ht : t₀ ∈ GluingDatum.incidentEdges x) (htc : t₀ ≠ contracted) (s t : Fin degree) :
    (data.vertexPartition x).Rel s t ↔ (mergedPartition data a b).Rel s t ∧
      ((mergedPartition data a b).Rel block.1 s →
        (data.edgePartition t₀).Rel s t ∨ (NP L t₀ s ∧ NP L t₀ t)) := by
  by_cases hs : (mergedPartition data a b).Rel block.1 s
  · rw [rel_on fd H Hd L hx ht htc hs]
    exact ⟨fun h ↦ ⟨h.1, fun _ ↦ h.2⟩, fun h ↦ ⟨h.1, h.2 hs⟩⟩
  · rw [rel_off fd Hd hx hs]
    exact ⟨fun h ↦ ⟨h, fun h' ↦ absurd h' hs⟩, fun h ↦ h.1⟩

include fd H in
/-- On the anchor, a sheet is a non-pass class over `x` exactly when its constituent over `x`
is trivalent. -/
theorem np_iff_nd {x : target.V} (hx : x = a ∨ x = b) {t₀ : target.edges}
    (ht : t₀ ∈ GluingDatum.incidentEdges x) (htc : t₀ ≠ contracted) {s : Fin degree}
    (hs : (mergedPartition data a b).Rel block.1 s) :
    NP L t₀ s ↔ nonDanglingValency data (data.sourceEndpoint x s) = 3 := by
  classical
  have hEref := edgePartition_refines_of_mem_incidentEdges data x t₀ ht
  have hX := endpoint_mem_fib fd H hx ht htc hs
  constructor
  · rintro ⟨i, hit, hip, his⟩
    obtain ⟨Xk, hXk, hk⟩ := ValencyTwoSplit.exists_home L H.compat i
    have hkinc := ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hk).1).2
    have hXx : Xk.1.1 = x := side_of_target hXk hx ht htc
      (hit ▸ target_mem_incidentEdges data hkinc)
    have h3 : nonDanglingValency data Xk = 3 := by
      have hb := DivInput.nd_bounds fd hXk
      have := (ValencyTwoSplit.passAt_iff_home L hXk hk).not.mp hip
      omega
    have hrel := ((incident_iff_target_mem_and_rel data _ _).mp hkinc).2
    rw [hXx] at hrel
    have hrel' := hrel.trans (hEref.rel his)
    have hEq : data.sourceEndpoint x s = Xk :=
      (data.sourceEndpoint_eq_iff _ _ _).mpr ⟨hXx.symm, hrel'.symm⟩
    rw [hEq]; exact h3
  · intro h3
    have hinc := incident_sourceEdge_sourceEndpoint data x t₀ ht s
    have hf : data.sourceEdge t₀ s ∈ bdAt data contracted (data.sourceEndpoint x s) :=
      (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨survive fd H
        (sourceVertexMap_endpoint hx hs) hinc htc, hinc⟩, htc⟩
    obtain ⟨i, hi⟩ := ValencyTwoSplit.exists_lift_eq L H.compat H.nd4 hX hf
    refine ⟨i, by rw [hi]; rfl, fun hp ↦ ?_, ?_⟩
    · have := (ValencyTwoSplit.passAt_iff_home L hX (hi ▸ hf)).mp hp
      omega
    · rw [hi]; exact (data.edgePartition t₀).rel_repr_left s

include fd H Hd in
/-- **Every anchor sheet is non-pass on some side**: two pass-throughs are never joined. -/
theorem np_or {ta tb : target.edges} (hta : ta ∈ GluingDatum.incidentEdges a)
    (htac : ta ≠ contracted) (htb : tb ∈ GluingDatum.incidentEdges b) (htbc : tb ≠ contracted)
    {s : Fin degree} (hs : (mergedPartition data a b).Rel block.1 s) :
    NP L ta s ∨ NP L tb s := by
  rw [np_iff_nd fd H L (Or.inl rfl) hta htac hs, np_iff_nd fd H L (Or.inr rfl) htb htbc hs]
  have hX := endpoint_mem_fib fd H (Or.inl rfl) hta htac hs
  have hY := endpoint_mem_fib fd H (Or.inr rfl) htb htbc hs
  have hca := contracted_mem_incidentEdges hc (Or.inl rfl)
  have hcb := contracted_mem_incidentEdges hc (Or.inr rfl)
  have h1 := incident_sourceEdge_sourceEndpoint data a contracted hca s
  have h2 := incident_sourceEdge_sourceEndpoint data b contracted hcb s
  have hnd : data.sourceEdge contracted s ∈ ndAt data (data.sourceEndpoint a s) :=
    (mem_ndAt data _ _).mpr ⟨Hd.survive fd hX h1, h1⟩
  have hnd' : data.sourceEdge contracted s ∈ ndAt data (data.sourceEndpoint b s) :=
    (mem_ndAt data _ _).mpr ⟨Hd.survive fd hY h2, h2⟩
  have hI := mem_intl_of_ndAt data hc hab hOne block hX hnd rfl
  have hXY : data.sourceEndpoint a s ≠ data.sourceEndpoint b s := fun h ↦
    hab (congrArg (fun X : data.SourceVertex ↦ X.1.1) h)
  by_cases h3 : nonDanglingValency data (data.sourceEndpoint a s) = 3
  · exact Or.inl h3
  · have h2' : nonDanglingValency data (data.sourceEndpoint a s) = 2 := by
      have := DivInput.nd_bounds fd hX; omega
    exact Or.inr (Hd.nd_three_of_attach fd hX h2' hY hI hnd hnd' hXY)

include fd H Hd in
/-- **At most one pass-through class over each endpoint**, in partition form. -/
theorem np_pass {x : target.V} (hx : x = a ∨ x = b) {t₀ : target.edges}
    (ht : t₀ ∈ GluingDatum.incidentEdges x) (htc : t₀ ≠ contracted) {s t : Fin degree}
    (hs : (mergedPartition data a b).Rel block.1 s) (hns : ¬ NP L t₀ s)
    (ht' : (mergedPartition data a b).Rel block.1 t) (hnt : ¬ NP L t₀ t) :
    (data.edgePartition t₀).Rel s t := by
  classical
  rw [np_iff_nd fd H L hx ht htc hs] at hns
  rw [np_iff_nd fd H L hx ht htc ht'] at hnt
  have hX := endpoint_mem_fib fd H hx ht htc hs
  have hY := endpoint_mem_fib fd H hx ht htc ht'
  have h2 : nonDanglingValency data (data.sourceEndpoint x s) = 2 := by
    have := DivInput.nd_bounds fd hX; omega
  have h2' : nonDanglingValency data (data.sourceEndpoint x t) = 2 := by
    have := DivInput.nd_bounds fd hY; omega
  have hEq := Hd.pass_unique fd hX hY h2 h2' rfl
  have hinc := incident_sourceEdge_sourceEndpoint data x t₀ ht s
  have hinc' := incident_sourceEdge_sourceEndpoint data x t₀ ht t
  rw [← hEq] at hinc'
  have hf : data.sourceEdge t₀ s ∈ bdAt data contracted (data.sourceEndpoint x s) :=
    (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨Hd.survive fd hX hinc, hinc⟩, htc⟩
  have hg : data.sourceEdge t₀ t ∈ bdAt data contracted (data.sourceEndpoint x s) :=
    (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨Hd.survive fd hX hinc', hinc'⟩, htc⟩
  have hfg := Finset.card_le_one.mp (le_of_eq (Hd.pass_cards fd hX h2).2) _ hf _ hg
  exact congrArg (fun e : data.SourceEdge ↦ e.1.2) hfg

include fd H Hd in
/-- The endpoint partition in limit coordinates. -/
theorem side_rel_lim {x : target.V} (hx : x = a ∨ x = b) {t₀ : target.edges}
    (ht : t₀ ∈ GluingDatum.incidentEdges x) (htc : t₀ ≠ contracted) (s t : Fin degree) :
    (data.vertexPartition x).Rel s t ↔
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel s t ∧
      (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 s →
        ((contractDatum data hc hab hOne).edgePartition (foldEdge hc hab hOne ⟨t₀, htc⟩)).Rel s t ∨
          (NPlim L (foldEdge hc hab hOne ⟨t₀, htc⟩) s ∧
            NPlim L (foldEdge hc hab hOne ⟨t₀, htc⟩) t)) := by
  rw [contractDatum_vertexPartition_merge, contractDatum_edgePartition_foldEdge,
    ← np_iff_nplim L, ← np_iff_nplim L, unfoldEdge_foldEdge]
  exact side_rel fd H L Hd hx ht htc s t

include fd H Hd in
/-- **The `(2,2)` package**: at any placement, the hypotheses of `transport_div` for one cover,
with `Dl`, `Dr` the wall occurrences on the retained and fresh sides. -/
theorem div_package (sec : (contract target hab hOne).edges → Bool)
    (hP : Placed hc hab hOne sec) :
    ∃ Dl Dr : (contract target hab hOne).edges,
      (∀ e, e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ ↔
        e = Dl ∨ e = Dr) ∧ sec Dl = false ∧ sec Dr = true ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).left.Rel s t ↔
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel s t ∧
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 s →
          ((contractDatum data hc hab hOne).edgePartition Dl).Rel s t ∨
            (NPlim L Dl s ∧ NPlim L Dl t))) ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right.Rel s t ↔
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel s t ∧
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 s →
          ((contractDatum data hc hab hOne).edgePartition Dr).Rel s t ∨
            (NPlim L Dr s ∧ NPlim L Dr t))) ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).newEdge.Rel s t ↔
        (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).left.Rel s t ∧
          (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right.Rel s t) ∧
      (∀ s, ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 s →
        NPlim L Dl s ∨ NPlim L Dr s) ∧
      (∀ x y, ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 x →
        ¬ NPlim L Dr x → ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 y →
          ¬ NPlim L Dr y → ((contractDatum data hc hab hOne).edgePartition Dr).Rel x y) := by
  classical
  obtain ⟨ta, hta, htac⟩ := exists_other_edge (contracted := contracted) Hd.a2
  obtain ⟨tb, htb, htbc⟩ := exists_other_edge (contracted := contracted) Hd.b2
  set Fa := foldEdge hc hab hOne ⟨ta, htac⟩
  set Fb := foldEdge hc hab hOne ⟨tb, htbc⟩
  have hMc : (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ = mergedPartition data a b :=
    contractDatum_vertexPartition_merge data hc hab hOne
  have hRa : IncomingTargetExpansion.right hc hab hOne Fa = false := right_foldEdge_a hc hab hOne hta htac
  have hRb : IncomingTargetExpansion.right hc hab hOne Fb = true := right_foldEdge_b hc hab hOne htb htbc
  have hFab : Fa ≠ Fb := fun h ↦ by rw [h, hRb] at hRa; exact Bool.noConfusion hRa
  have hwall : ∀ e, e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ ↔
      e = Fa ∨ e = Fb := by
    have hsub : ({Fa, Fb} : Finset _) ⊆
        GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact foldEdge_mem_wall hc hab hOne htac (Or.inl hta)
      · rw [Finset.mem_singleton.mp he]; exact foldEdge_mem_wall hc hab hOne htbc (Or.inr htb)
    have hEq := Finset.eq_of_subset_of_card_le hsub (by rw [H.valency, Finset.card_pair hFab])
    intro e
    rw [← hEq]; simp
  have hA_lim : ∀ z, ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 z ↔
      (mergedPartition data a b).Rel block.1 z := by intro z; rw [hMc]
  have hnpor : ∀ z, ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 z →
      NPlim L Fa z ∨ NPlim L Fb z := by
    intro z hz
    rw [← np_iff_nplim L, ← np_iff_nplim L, unfoldEdge_foldEdge, unfoldEdge_foldEdge]
    exact np_or fd H L Hd hta htac htb htbc ((hA_lim z).mp hz)
  have hpass : ∀ {x : target.V} (hx : x = a ∨ x = b) {t₀ : target.edges}
      (ht : t₀ ∈ GluingDatum.incidentEdges x) (htc : t₀ ≠ contracted) (y z : Fin degree),
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 y →
      ¬ NPlim L (foldEdge hc hab hOne ⟨t₀, htc⟩) y →
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 z →
      ¬ NPlim L (foldEdge hc hab hOne ⟨t₀, htc⟩) z →
      ((contractDatum data hc hab hOne).edgePartition (foldEdge hc hab hOne ⟨t₀, htc⟩)).Rel y z := by
    intro x hx t₀ ht htc y z hy hny hz hnz
    rw [← np_iff_nplim L, unfoldEdge_foldEdge] at hny hnz
    rw [contractDatum_edgePartition_foldEdge]
    exact np_pass fd H L Hd hx ht htc ((hA_lim y).mp hy) hny ((hA_lim z).mp hz) hnz
  have hnewRel := contracted_rel fd H Hd
  obtain ⟨hnew, hpos, hneg⟩ := resolution_eq fd hc hab hOne sec hP
  by_cases hsup : ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne e = sec e
  · obtain ⟨hl, hr⟩ := hpos hsup
    refine ⟨Fa, Fb, hwall, ?_, ?_, ?_, ?_, ?_, hnpor, hpass (Or.inr rfl) htb htbc⟩
    · rw [← hsup Fa ((hwall Fa).mpr (Or.inl rfl)), hRa]
    · rw [← hsup Fb ((hwall Fb).mpr (Or.inr rfl)), hRb]
    · intro s t; rw [hl]; exact side_rel_lim fd H L Hd (Or.inl rfl) hta htac s t
    · intro s t; rw [hr]; exact side_rel_lim fd H L Hd (Or.inr rfl) htb htbc s t
    · intro s t; rw [hnew, hl, hr]; exact hnewRel s t
  · have hflip : ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = !(sec e) := hP.resolve_left hsup
    obtain ⟨hl, hr⟩ := hneg hsup
    refine ⟨Fb, Fa, fun e ↦ (hwall e).trans or_comm, ?_, ?_, ?_, ?_, ?_,
      fun z hz ↦ (hnpor z hz).symm, hpass (Or.inl rfl) hta htac⟩
    · have h1 := hflip Fb ((hwall Fb).mpr (Or.inr rfl))
      rw [hRb] at h1
      cases hsb : sec Fb
      · rfl
      · rw [hsb] at h1; exact absurd h1 (by decide)
    · have h1 := hflip Fa ((hwall Fa).mpr (Or.inl rfl))
      rw [hRa] at h1
      cases hsa : sec Fa
      · rw [hsa] at h1; exact absurd h1 (by decide)
      · rfl
    · intro s t; rw [hl]; exact side_rel_lim fd H L Hd (Or.inr rfl) htb htbc s t
    · intro s t; rw [hr]; exact side_rel_lim fd H L Hd (Or.inl rfl) hta htac s t
    · intro s t; rw [hnew, hl, hr, and_comm]; exact hnewRel s t

end DivPackage

/-! ## 8.  The leaf package: the hypotheses of `transport_leaf` read off one cover -/

section LeafPackage

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  {u v : target.V}
  (H : AnchorInput data hc hab hOne block) (Hl : LeafInput data hc hab hOne block u v)
  (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

include fd Hl in
/-- A trivalent constituent over the trivalent endpoint carries an internal occurrence. -/
theorem tri_ndOver_nonempty {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hXv : X.1.1 = v) : (ndOver data X contracted).Nonempty := by
  classical
  have hr : ram data X = 0 :=
    W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd X (by rw [hXv]; exact Hl.chv)
  have h3 := Hl.nd_three fd hX hXv
  have hbd : (bdAt data contracted X).card ≤ 2 := by
    have htargets : ∀ f ∈ bdAt data contracted X, f.1.1 ∈
        (GluingDatum.incidentEdges v).erase contracted := by
      intro f hf
      obtain ⟨hf1, hf2⟩ := (mem_bdAt data _ _).mp hf
      have := target_mem_incidentEdges data ((mem_ndAt data _ _).mp hf1).2
      rw [hXv] at this
      exact Finset.mem_erase.mpr ⟨hf2, this⟩
    have hcard : ((GluingDatum.incidentEdges v).erase contracted).card = 2 := by
      rw [Finset.card_erase_of_mem (contracted_mem_incidentEdges hc (side_of_huv hab Hl.huv).2.1),
        Hl.v3]
    have hinj : Set.InjOn (fun f : data.SourceEdge ↦ f.1.1) (bdAt data contracted X) := by
      intro f hf g hg hfg
      exact ValencyThreeSplit.eq_of_ram_zero data fd hr ((mem_bdAt data _ _).mp hf).1
        ((mem_bdAt data _ _).mp hg).1 hfg
    have := Finset.card_le_card_of_injOn _ htargets hinj
    omega
  have hsplit := ValencyThreeSplit.card_ndAt_split data (contracted := contracted) X
  exact Finset.card_pos.mp (by omega)

include fd H Hl in
/-- **The leaf package**: at the placement putting both wall occurrences on the fresh side, the
hypotheses of `transport_leaf` for one cover, with `Dt` the direction of the label `0`. -/
theorem leaf_package (sec : (contract target hab hOne).edges → Bool)
    (hP : Placed hc hab hOne sec)
    (hsec : ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      sec e = true) :
    ∃ D₃ : (contract target hab hOne).edges,
      (∀ e, e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ ↔
        e = (L.e 0).1.1 ∨ e = D₃) ∧
      ∃ ℓ₁ ℓ₂ : Fin degree, ℓ₁ ≠ ℓ₂ ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).left.Rel s t ↔
        s = t ∨ ((s = ℓ₁ ∨ s = ℓ₂) ∧ (t = ℓ₁ ∨ t = ℓ₂))) ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right.Rel s t ↔
        ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel s t ∧
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 s →
          ((contractDatum data hc hab hOne).edgePartition (L.e 0).1.1).Rel s t)) ∧
      (∀ s t, (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).newEdge.Rel s t ↔
        s = t) ∧
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 ℓ₁ ∧
      ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 ℓ₂ ∧
      ¬ (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right.Rel ℓ₁ ℓ₂ ∧
      (∀ x, ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 x →
        (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right.Rel ℓ₁ x ∨
          (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right.Rel ℓ₂ x) := by
  classical
  obtain ⟨huw, hvw, huv'⟩ := side_of_huv hab Hl.huv
  have hMc : (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ = mergedPartition data a b :=
    contractDatum_vertexPartition_merge data hc hab hOne
  -- the wall: both occurrences come from `v`
  have hwallv : ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      unfoldEdge hc hab hOne e ∈ GluingDatum.incidentEdges v := by
    intro e he
    have hne := unfoldEdge_ne_contracted hc hab hOne e
    rcases ValencyThreeResolutionMatch.unfold_mem_ends (hc := hc) he with h | h <;>
      rcases Hl.huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp Hl.u1
      have hcu := contracted_mem_incidentEdges hc (Or.inl rfl)
      rw [ht, Finset.mem_singleton] at h hcu
      exact hne (h.trans hcu.symm)
    · exact h
    · exact h
    · exfalso
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp Hl.u1
      have hcu := contracted_mem_incidentEdges hc (Or.inr rfl)
      rw [ht, Finset.mem_singleton] at h hcu
      exact hne (h.trans hcu.symm)
  have hDt : (L.e 0).1.1 ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
    target_mem_incidentEdges _ ((mem_ndAt _ _ _).mp (L.mem 0)).2
  obtain ⟨D₃, hD₃, hD₃ne⟩ := Finset.exists_mem_ne (by rw [H.valency]; norm_num : 1 <
    (GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩).card) (L.e 0).1.1
  have hwall : ∀ e, e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ ↔
      e = (L.e 0).1.1 ∨ e = D₃ := by
    have hsub : ({(L.e 0).1.1, D₃} : Finset _) ⊆
        GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hDt
      · rw [Finset.mem_singleton.mp he]; exact hD₃
    have hEq := Finset.eq_of_subset_of_card_le hsub
      (by rw [H.valency, Finset.card_pair hD₃ne.symm])
    intro e
    rw [← hEq]; simp
  -- the resolution's two endpoints
  obtain ⟨hnew, hpos, hneg⟩ := resolution_eq fd hc hab hOne sec hP
  have hlr : (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).left =
        data.vertexPartition u ∧
      (M11WallExhaustion.incomingResolution data hc hab hOne sec hP).right =
        data.vertexPartition v := by
    rcases Hl.huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine hpos fun e he ↦ ?_
      rw [hsec e he, eq_foldEdge_unfold hc hab hOne e]
      exact right_foldEdge_b hc hab hOne (hwallv e he) _
    · refine hneg fun h ↦ ?_
      have h1 := h _ hDt
      rw [hsec _ hDt, eq_foldEdge_unfold hc hab hOne (L.e 0).1.1,
        right_foldEdge_a hc hab hOne (hwallv _ hDt)] at h1
      exact Bool.false_ne_true h1
  obtain ⟨hl, hr⟩ := hlr
  obtain ⟨ℓ₁, ℓ₂, h12, hℓ₁, hℓ₂, hℓv, hurel⟩ := leaf_rel fd H Hl
  set t₀ := unfoldEdge hc hab hOne (L.e 0).1.1
  have ht₀ : t₀ ∈ GluingDatum.incidentEdges v := hwallv _ hDt
  have ht₀c : t₀ ≠ contracted := unfoldEdge_ne_contracted hc hab hOne _
  refine ⟨D₃, hwall, ℓ₁, ℓ₂, h12, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t; rw [hl]; exact hurel s t
  · intro s t
    rw [hr, hMc, limit_edgePartition hc hab hOne]
    exact tri_rel fd H Hl ht₀ ht₀c s t
  · intro s t; rw [hnew]; exact contracted_rel_leaf fd H Hl s t
  · rw [hMc]; exact hℓ₁
  · rw [hMc]; exact hℓ₂
  · rw [hr]; exact hℓv
  · -- every anchor sheet lies in one of the two constituents over `v` the fold meets
    intro x hx
    rw [hMc] at hx
    rw [hr]
    have hX := endpoint_mem_fib fd H hvw ht₀ ht₀c hx
    obtain ⟨e, he⟩ := tri_ndOver_nonempty fd Hl hX rfl
    obtain ⟨heX, heT⟩ := (mem_ndOver data _ _ _).mp he
    have heI := mem_intl_of_ndAt data hc hab hOne block hX heX heT
    obtain ⟨Q, hQ, heQ, hQs, -⟩ := DivInput.exists_other_end heI ((mem_ndAt data _ _).mp heX).2
    have hQu : Q.1.1 = u := by
      rcases Hl.side hQ with h | h
      · exact h
      · exact absurd h hQs
    -- the sheet of `e` lies in the fold's pair
    have hQsz : 2 ≤ size data Q := by
      have hnd2 := ValencyThreeSplit.nonDanglingValency_two_le data fd
        ((mem_fib_iff data hc hab hOne block Q).mp hQ).2.2
      have hnd := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data Q
      have hLe := StableLocalProperties.card_incidentSourceEdge_le_blockCard_of_target_leaf data Q
        (by rw [hQu]; exact Hl.u1)
      have : (2 : ℤ) ≤ Fintype.card (IncidentSourceEdge data Q) := by exact_mod_cast hnd2.trans hnd
      have h' : (2 : ℤ) ≤ size data Q := this.trans hLe
      exact_mod_cast h'
    have heQrel : (data.vertexPartition u).Rel Q.1.2 e.1.2 := by
      have := ((incident_iff_target_mem_and_rel data _ _).mp ((mem_ndAt data _ _).mp heQ).2).2
      rwa [hQu] at this
    have hQsz' : 1 < ((data.vertexPartition Q.1.1).block Q.1.2).card :=
      lt_of_lt_of_le (by norm_num) hQsz
    obtain ⟨r', hr', hr'e⟩ := Finset.exists_mem_ne hQsz' e.1.2
    have hr'rel : (data.vertexPartition u).Rel e.1.2 r' := by
      rw [SheetPartition.mem_block_iff] at hr'
      rw [hQu] at hr'
      exact heQrel.symm.trans hr'
    have hepair : e.1.2 = ℓ₁ ∨ e.1.2 = ℓ₂ := by
      rcases (hurel _ _).mp hr'rel with h | ⟨h, -⟩
      · exact absurd h.symm hr'e
      · exact h
    have heXrel : (data.vertexPartition v).Rel x e.1.2 := by
      have h1 := ((incident_iff_target_mem_and_rel data _ _).mp ((mem_ndAt data _ _).mp heX).2).2
      have h2 : (data.vertexPartition v).Rel ((data.vertexPartition v).repr x) x :=
        (data.vertexPartition v).rel_repr_left x
      exact h2.symm.trans h1
    rcases hepair with h | h
    · left; rw [← h]; exact heXrel.symm
    · right; rw [← h]; exact heXrel.symm

include fd Hl in
/-- **Paired survivors span the same sheets**, in limit coordinates. -/
theorem paired_rel_lim {i j : Fin 4} (hP : Paired L i j) (x : Fin degree) :
    ((contractDatum data hc hab hOne).edgePartition (L.e i).1.1).Rel (L.e i).1.2 x ↔
      ((contractDatum data hc hab hOne).edgePartition (L.e j).1.1).Rel (L.e j).1.2 x := by
  rw [limit_edgePartition hc hab hOne, limit_edgePartition hc hab hOne, label_unfold L i,
    label_unfold L j, label_sheet L i, label_sheet L j]
  exact paired_rel_iff fd Hl L hP x

include fd H Hl in
/-- **Every anchor sheet lies in a survivor class of each wall occurrence**, and that survivor
has a partner, paired with it, in the other direction. -/
theorem exists_label_partner {D D' : (contract target hab hOne).edges}
    (hwall : ∀ e, e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ ↔
      e = D ∨ e = D') (hDD' : D ≠ D') {s : Fin degree}
    (hs : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel block.1 s) :
    ∃ i j, (L.e i).1.1 = D ∧ (L.e j).1.1 = D' ∧ Paired L i j ∧
      ((contractDatum data hc hab hOne).edgePartition D).Rel (L.e i).1.2 s := by
  classical
  obtain ⟨huw, hvw, huv'⟩ := side_of_huv hab Hl.huv
  have hMc : (contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩ = mergedPartition data a b :=
    contractDatum_vertexPartition_merge data hc hab hOne
  rw [hMc] at hs
  have hDmem := (hwall D).mpr (Or.inl rfl)
  set t₀ := unfoldEdge hc hab hOne D
  have ht₀c : t₀ ≠ contracted := unfoldEdge_ne_contracted hc hab hOne D
  have ht₀ : t₀ ∈ GluingDatum.incidentEdges v := by
    have hne := unfoldEdge_ne_contracted hc hab hOne D
    rcases ValencyThreeResolutionMatch.unfold_mem_ends (hc := hc) hDmem with h | h <;>
      rcases Hl.huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp Hl.u1
      have hcu := contracted_mem_incidentEdges hc (Or.inl rfl)
      rw [ht, Finset.mem_singleton] at h hcu
      exact hne (h.trans hcu.symm)
    · exact h
    · exact h
    · exfalso
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp Hl.u1
      have hcu := contracted_mem_incidentEdges hc (Or.inr rfl)
      rw [ht, Finset.mem_singleton] at h hcu
      exact hne (h.trans hcu.symm)
  have hX := endpoint_mem_fib fd H hvw ht₀ ht₀c hs
  have hinc := incident_sourceEdge_sourceEndpoint data v t₀ ht₀ s
  have hf : data.sourceEdge t₀ s ∈ bdAt data contracted (data.sourceEndpoint v s) :=
    (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨survive fd H
      (sourceVertexMap_endpoint hvw hs) hinc ht₀c, hinc⟩, ht₀c⟩
  obtain ⟨i, hi⟩ := ValencyTwoSplit.exists_lift_eq L H.compat H.nd4 hX hf
  obtain ⟨g, hg, hgT⟩ := Hl.exists_partner fd hX hf
  obtain ⟨j, hj⟩ := ValencyTwoSplit.exists_lift_eq L H.compat H.nd4 hX hg
  have hDi : (L.e i).1.1 = D := by
    apply unfoldEdge_injective (hc := hc) (hab := hab) (hOne := hOne)
    rw [label_unfold L i, hi]; rfl
  have hDj : (L.e j).1.1 = D' := by
    have hmem : (L.e j).1.1 ∈ GluingDatum.incidentEdges (target := contract target hab hOne)
        ⟨a, hab⟩ := target_mem_incidentEdges _ ((mem_ndAt _ _ _).mp (L.mem j)).2
    rcases (hwall _).mp hmem with h | h
    · exfalso
      apply hgT
      rw [← hj, ← label_unfold L j, h]
      rfl
    · exact h
  refine ⟨i, j, hDi, hDj, ⟨_, hX, _, hX, hi ▸ ((mem_bdAt data _ _).mp hf).1,
    hj ▸ ((mem_bdAt data _ _).mp hg).1, Or.inl rfl⟩, ?_⟩
  rw [limit_edgePartition hc hab hOne, label_sheet L i, hi]
  exact (data.edgePartition t₀).rel_repr_left s

omit [Fintype coordinate] [DecidableEq coordinate] in
include Hl in
/-- At a leaf split both wall occurrences come from the trivalent endpoint. -/
theorem wall_at_v {e : (contract target hab hOne).edges}
    (he : e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩) :
    unfoldEdge hc hab hOne e ∈ GluingDatum.incidentEdges v := by
  have hne := unfoldEdge_ne_contracted hc hab hOne e
  rcases ValencyThreeResolutionMatch.unfold_mem_ends (hc := hc) he with h | h <;>
    rcases Hl.huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp Hl.u1
    have hcu := contracted_mem_incidentEdges hc (Or.inl rfl)
    rw [ht, Finset.mem_singleton] at h hcu
    exact hne (h.trans hcu.symm)
  · exact h
  · exact h
  · exfalso
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp Hl.u1
    have hcu := contracted_mem_incidentEdges hc (Or.inr rfl)
    rw [ht, Finset.mem_singleton] at h hcu
    exact hne (h.trans hcu.symm)

omit [Fintype coordinate] [DecidableEq coordinate] in
include Hl in
/-- **At a leaf split, the placement putting both wall occurrences on the fresh side.** -/
theorem placed_true : Placed hc hab hOne (fun _ ↦ true) := by
  rcases Hl.huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    intro e he
    rw [eq_foldEdge_unfold hc hab hOne e]
    exact right_foldEdge_b hc hab hOne (wall_at_v Hl he) _
  · right
    intro e he
    rw [eq_foldEdge_unfold hc hab hOne e]
    exact right_foldEdge_a hc hab hOne (wall_at_v Hl he) _

end LeafPackage

/-! ## 9.  Two covers: the placements and the transports -/

section TwoCovers

open ValencyThreeResolutionMatch (ends_of_mem mem_of_ends)
open W3Nd2StarExhaustionProof (edge_rel_iff incident_iff)

variable {degree : ℕ} {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {target₁ target₂ : CFGraph}
  {data₁ : GluingDatum target₁ degree} {data₂ : GluingDatum target₂ degree}
  (fd₁ : FullDimensionalSourcePresentation data₁ coordinate)
  (fd₂ : FullDimensionalSourcePresentation data₂ coordinate)
  {a₁ b₁ : target₁.V} {contracted₁ : target₁.edges}
  {hc₁ : (contracted₁ : target₁.V × target₁.V) = (a₁, b₁)} {hab₁ : a₁ ≠ b₁}
  {hOne₁ : num_edges target₁ a₁ b₁ = 1} {block₁ : (mergedPartition data₁ a₁ b₁).Blocks}
  {a₂ b₂ : target₂.V} {contracted₂ : target₂.edges}
  {hc₂ : (contracted₂ : target₂.V × target₂.V) = (a₂, b₂)} {hab₂ : a₂ ≠ b₂}
  {hOne₂ : num_edges target₂ a₂ b₂ = 1} {block₂ : (mergedPartition data₂ a₂ b₂).Blocks}
  (H₁ : AnchorInput data₁ hc₁ hab₁ hOne₁ block₁) (H₂ : AnchorInput data₂ hc₂ hab₂ hOne₂ block₂)
  (ψ : GeometricDatumIso (contractDatum data₁ hc₁ hab₁ hOne₁) (contractDatum data₂ hc₂ hab₂ hOne₂))
  (hWall : ψ.targetVertex ⟨a₁, hab₁⟩ = ⟨a₂, hab₂⟩)
  (hA : ((contractDatum data₂ hc₂ hab₂ hOne₂).vertexPartition ⟨a₂, hab₂⟩).Rel block₂.1
    (ψ.vertexPerm ⟨a₁, hab₁⟩ block₁.1))
  (L₁ : Labelling (contractDatum data₁ hc₁ hab₁ hOne₁) (limA data₁ hc₁ hab₁ hOne₁ block₁))
  (L₂ : Labelling (contractDatum data₂ hc₂ hab₂ hOne₂) (limA data₂ hc₂ hab₂ hOne₂ block₂))
  (hL : ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i))

include hWall in
theorem mem_wall_map (e : (contract target₁ hab₁ hOne₁).edges) :
    e ∈ GluingDatum.incidentEdges (target := contract target₁ hab₁ hOne₁) ⟨a₁, hab₁⟩ ↔
      ψ.targetEdge e ∈ GluingDatum.incidentEdges (target := contract target₂ hab₂ hOne₂) ⟨a₂, hab₂⟩ :=
  ⟨fun h ↦ (incident_iff ψ hWall e).mp (ends_of_mem h),
    fun h ↦ mem_of_ends ((incident_iff ψ hWall e).mpr h)⟩

include hL in
theorem label_target_map (i : Fin 4) : (L₂.e i).1.1 = ψ.targetEdge (L₁.e i).1.1 :=
  congrArg (fun x : (contractDatum data₂ hc₂ hab₂ hOne₂).SourceEdge ↦ x.1.1) (hL i)

include hL in
theorem label_sheet_map (i : Fin 4) : (L₂.e i).1.2 = ψ.edgePerm (L₁.e i).1.1 (L₁.e i).1.2 :=
  congrArg (fun x : (contractDatum data₂ hc₂ hab₂ hOne₂).SourceEdge ↦ x.1.2) (hL i)

include hL in
/-- **The non-pass predicate transports** along the limit isomorphism, for transported labels
and the same pass-throughs. -/
theorem nplim_map (hpass : ∀ i, PassAt L₁ i ↔ PassAt L₂ i)
    (D : (contract target₁ hab₁ hOne₁).edges) (s : Fin degree) :
    NPlim L₁ D s ↔ NPlim L₂ (ψ.targetEdge D) (ψ.edgePerm D s) := by
  unfold NPlim
  refine exists_congr fun i ↦ ?_
  have hLe := label_target_map ψ L₁ L₂ hL i
  have hLm := label_sheet_map ψ L₁ L₂ hL i
  constructor
  · rintro ⟨hD, hp, hr⟩
    subst hD
    refine ⟨hLe, (hpass i).not.mp hp, ?_⟩
    rw [hLm]
    exact (edge_rel_iff ψ _ _ _).mp hr
  · rintro ⟨hD, hp, hr⟩
    have hD' : (L₁.e i).1.1 = D := ψ.targetEdge.injective (hLe.symm.trans hD)
    subst hD'
    refine ⟨rfl, (hpass i).not.mpr hp, ?_⟩
    rw [hLm] at hr
    exact (edge_rel_iff ψ _ _ _).mpr hr

include fd₁ fd₂ H₁ H₂ hWall hA hL in
/-- **The transport between two `(2,2)` covers with the same pass-throughs.** -/
theorem transport_divDiv (Hd₁ : DivInput data₁ hc₁ hab₁ hOne₁ block₁)
    (Hd₂ : DivInput data₂ hc₂ hab₂ hOne₂ block₂) (hpass : ∀ i, PassAt L₁ i ↔ PassAt L₂ i) :
    ∃ (sec₁ : (contract target₁ hab₁ hOne₁).edges → Bool) (hP₁ : Placed hc₁ hab₁ hOne₁ sec₁)
      (sec₂ : (contract target₂ hab₂ hOne₂).edges → Bool) (hP₂ : Placed hc₂ hab₂ hOne₂ sec₂),
      Nonempty (ResolutionExpansionFree.TransportFree ψ ⟨a₁, hab₁⟩ ⟨a₂, hab₂⟩ sec₁ sec₂
        (M11WallExhaustion.incomingResolution data₁ hc₁ hab₁ hOne₁ sec₁ hP₁)
        (M11WallExhaustion.incomingResolution data₂ hc₂ hab₂ hOne₂ sec₂ hP₂)) := by
  classical
  set sec₁ := IncomingTargetExpansion.right hc₁ hab₁ hOne₁
  have hP₁ : Placed hc₁ hab₁ hOne₁ sec₁ := Or.inl fun _ _ ↦ rfl
  obtain ⟨Dl, Dr, hW₁, hsl, hsr, h1l, h1r, h1n, h1or, -⟩ := div_package fd₁ H₁ L₁ Hd₁ sec₁ hP₁
  -- the natural placement of the second cover, to see which way `ψ` sends the two sides
  obtain ⟨El, Er, hW₂, hel, her, -⟩ := div_package fd₂ H₂ L₂ Hd₂
    (IncomingTargetExpansion.right hc₂ hab₂ hOne₂) (Or.inl fun _ _ ↦ rfl)
  set sec₂ : (contract target₂ hab₂ hOne₂).edges → Bool := fun e ↦ sec₁ (ψ.targetEdge.symm e)
  have hs₂l : sec₂ (ψ.targetEdge Dl) = false := by simp [sec₂, hsl]
  have hs₂r : sec₂ (ψ.targetEdge Dr) = true := by simp [sec₂, hsr]
  have hψDl := (mem_wall_map ψ hWall Dl).mp ((hW₁ Dl).mpr (Or.inl rfl))
  have hψDr := (mem_wall_map ψ hWall Dr).mp ((hW₁ Dr).mpr (Or.inr rfl))
  have hDlr : ψ.targetEdge Dl ≠ ψ.targetEdge Dr := fun h ↦ by
    rw [ψ.targetEdge.injective h, hsr] at hsl; exact Bool.noConfusion hsl
  have hW₂' : ∀ e, e ∈ GluingDatum.incidentEdges (target := contract target₂ hab₂ hOne₂) ⟨a₂, hab₂⟩ ↔
      e = ψ.targetEdge Dl ∨ e = ψ.targetEdge Dr := by
    intro e
    rw [← ψ.targetEdge.apply_symm_apply e, ← mem_wall_map ψ hWall, hW₁,
      ψ.targetEdge.apply_symm_apply, ψ.targetEdge.symm_apply_eq, ψ.targetEdge.symm_apply_eq]
  have hP₂ : Placed hc₂ hab₂ hOne₂ sec₂ := by
    rcases (hW₂ (ψ.targetEdge Dl)).mp hψDl with h | h
    · -- `ψ` keeps the sides
      have h' : ψ.targetEdge Dr = Er := by
        rcases (hW₂ (ψ.targetEdge Dr)).mp hψDr with h' | h'
        · exact absurd (h.trans h'.symm) hDlr
        · exact h'
      left
      intro e he
      rcases (hW₂' e).mp he with rfl | rfl
      · rw [h, hel, ← h, hs₂l]
      · rw [h', her, ← h', hs₂r]
    · -- `ψ` exchanges the sides
      have h' : ψ.targetEdge Dr = El := by
        rcases (hW₂ (ψ.targetEdge Dr)).mp hψDr with h' | h'
        · exact h'
        · exact absurd (h.trans h'.symm) hDlr
      right
      intro e he
      rcases (hW₂' e).mp he with rfl | rfl
      · rw [h, her, ← h, hs₂l]; rfl
      · rw [h', hel, ← h', hs₂r]; rfl
  obtain ⟨Dl', Dr', hW₂'', hsl', hsr', h2l, h2r, h2n, h2or, h2pass⟩ :=
    div_package fd₂ H₂ L₂ Hd₂ sec₂ hP₂
  have hDl' : Dl' = ψ.targetEdge Dl := by
    rcases (hW₂' Dl').mp ((hW₂'' Dl').mpr (Or.inl rfl)) with h | h
    · exact h
    · rw [h, hs₂r] at hsl'; exact absurd hsl' (by decide)
  have hDr' : Dr' = ψ.targetEdge Dr := by
    rcases (hW₂' Dr').mp ((hW₂'' Dr').mpr (Or.inr rfl)) with h | h
    · rw [h, hs₂l] at hsr'; exact absurd hsr' (by decide)
    · exact h
  subst hDl' hDr'
  refine ⟨sec₁, hP₁, sec₂, hP₂, ?_⟩
  exact transport_div ψ hWall Dl Dr hW₁ sec₁ sec₂ hsl hsr (fun e ↦ by simp [sec₂]) block₁.1
    block₂.1 hA (NPlim L₁ Dl) (NPlim L₁ Dr) (NPlim L₂ (ψ.targetEdge Dl)) (NPlim L₂ (ψ.targetEdge Dr))
    _ _ h1l h1r h1n h1or h2l h2r h2n h2or h2pass (nplim_map ψ L₁ L₂ hL hpass Dl)
    (nplim_map ψ L₁ L₂ hL hpass Dr)

include fd₁ fd₂ H₁ H₂ hWall hA hL in
/-- **The transport between two leaf-split covers with the same pairing.** -/
theorem transport_leafLeaf {u₁ v₁ : target₁.V} {u₂ v₂ : target₂.V}
    (Hl₁ : LeafInput data₁ hc₁ hab₁ hOne₁ block₁ u₁ v₁)
    (Hl₂ : LeafInput data₂ hc₂ hab₂ hOne₂ block₂ u₂ v₂)
    (hpair : ∀ i j, Paired L₁ i j ↔ Paired L₂ i j) :
    Nonempty (ResolutionExpansionFree.TransportFree ψ ⟨a₁, hab₁⟩ ⟨a₂, hab₂⟩ (fun _ ↦ true)
      (fun _ ↦ true)
      (M11WallExhaustion.incomingResolution data₁ hc₁ hab₁ hOne₁ _ (placed_true Hl₁))
      (M11WallExhaustion.incomingResolution data₂ hc₂ hab₂ hOne₂ _ (placed_true Hl₂))) := by
  classical
  obtain ⟨D₃, hW₁, ℓ₁, ℓ₂, h12, h1l, h1r, h1n, hℓ₁, hℓ₂, hℓ, -⟩ :=
    leaf_package fd₁ H₁ Hl₁ L₁ _ (placed_true Hl₁) (fun _ _ ↦ rfl)
  obtain ⟨D₃', hW₂, ℓ₁', ℓ₂', h12', h2l, h2r, h2n, -, -, -, h2cover⟩ :=
    leaf_package fd₂ H₂ Hl₂ L₂ _ (placed_true Hl₂) (fun _ _ ↦ rfl)
  set Dt := (L₁.e 0).1.1
  have hLe0 := label_target_map ψ L₁ L₂ hL 0
  rw [hLe0] at h2r
  have hD₃ne : Dt ≠ D₃ := by
    intro h
    have hD₃mem := (hW₁ D₃).mpr (Or.inr rfl)
    have : (GluingDatum.incidentEdges (target := contract target₁ hab₁ hOne₁) ⟨a₁, hab₁⟩) ⊆ {Dt} := by
      intro e he
      rcases (hW₁ e).mp he with rfl | rfl
      · simp
      · rw [← h]; simp
    have hcard := Finset.card_le_card this
    rw [H₁.valency, Finset.card_singleton] at hcard
    omega
  refine transport_leaf ψ hWall Dt D₃ hW₁ (fun _ ↦ true) (fun _ ↦ true) (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) block₁.1 block₂.1 hA ℓ₁ ℓ₂ ℓ₁' ℓ₂' h12' _ _ h1l h1r h1n hℓ₁ hℓ₂ hℓ h2l h2r h2n
    h2cover ?_
  -- the cross condition, from the common pairing
  intro s hs
  obtain ⟨i, j, hDi, hDj, hPij, his⟩ := exists_label_partner fd₁ H₁ Hl₁ L₁ hW₁ hD₃ne hs
  have h1 := (paired_rel_lim fd₁ Hl₁ L₁ hPij s).mp (hDi ▸ his)
  rw [hDj] at h1
  have h2 := (edge_rel_iff ψ D₃ _ _).mp h1
  have hLej := label_target_map ψ L₁ L₂ hL j
  have hLmj := label_sheet_map ψ L₁ L₂ hL j
  have hLei := label_target_map ψ L₁ L₂ hL i
  have hLmi := label_sheet_map ψ L₁ L₂ hL i
  rw [hDj] at hLej hLmj
  rw [hDi] at hLei hLmi
  rw [← hLej, ← hLmj] at h2
  have h3 := (paired_rel_lim fd₂ Hl₂ L₂ ((hpair i j).mp hPij) (ψ.edgePerm D₃ s)).mpr h2
  rw [hLei, hLmi] at h3
  have h4 := (edge_rel_iff ψ Dt _ _).mp his
  exact h3.symm.trans h4

end TwoCovers

/-! ## 10.  `ResolutionMatch` at valency two, with no hypothesis -/

section Assembly

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyTwoSplit (RegrowthAnchor anchorOf Split Reads LeafCover)

variable {n p : ℕ}

/-- A `(2,2)` cover is not a leaf split. -/
theorem not_leafCover_of_div {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    {a b : target.V} {contracted : target.edges}
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
    (Hd : DivInput data hc hab hOne block) : ¬ LeafCover a b := by
  rintro (h | h)
  · rw [Hd.a2] at h; exact absurd h (by norm_num)
  · rw [Hd.b2] at h; exact absurd h (by norm_num)

/-- A leaf split is one. -/
theorem leafCover_of_leaf {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    {a b : target.V} {contracted : target.edges}
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks} {u v : target.V}
    (Hl : LeafInput data hc hab hOne block u v) : LeafCover a b := by
  rcases Hl.huv with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl Hl.u1
  · exact Or.inr Hl.u1

/-- **Stage 4 at valency two, `ResolutionMatch`, in general.**  At any core, request and
degree: two regrowths at valency-two anchors, a labelled-metric isomorphism `ψ` of their limits,
labellings transported along `ψ` and the same read split admit placements and a decoupled
transport of the two incoming resolutions, along `ψ` itself.  At a `(2,2)` split the retained
side is the one `ψ` matches (`transport_divDiv`); at a leaf split both wall occurrences are on
the fresh side (`transport_leafLeaf`).  A `(2,2)` cover and a leaf cover never read the same
split. -/
theorem resolutionMatch (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    ValencyTwoSplit.ResolutionMatch core y degree := by
  classical
  intro w w' block block' H H' ψ hψ L L' hL s hs hs'
  have hlim := ValencyTwoSplit.sourceVertexEquiv_limA w w' H H' ψ
  have hWall : ψ.targetVertex ⟨ValencyThreeRigidity.endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ =
      ⟨ValencyThreeRigidity.endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ :=
    congrArg (fun x : w'.limit.SourceVertex ↦ x.1.1) hlim
  have hA : (w'.limit.vertexPartition
      ⟨ValencyThreeRigidity.endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩).Rel block'.1
      (ψ.vertexPerm ⟨ValencyThreeRigidity.endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ block.1) := by
    have h2 : ψ.vertexPerm ⟨ValencyThreeRigidity.endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
        block.1 = block'.1 :=
      congrArg (fun x : w'.limit.SourceVertex ↦ x.1.2) hlim
    change (w'.limit.vertexPartition _).repr block'.1 =
      (w'.limit.vertexPartition _).repr (ψ.vertexPerm _ block.1)
    rw [h2]
  have hpass : ∀ i, PassAt L i ↔ PassAt L' i := fun i ↦ (hs.2.1 i).symm.trans (hs'.2.1 i)
  have hpair : ∀ i j, Paired L i j ↔ Paired L' i j := fun i j ↦ (hs.2.2 i j).symm.trans (hs'.2.2 i j)
  have hleaf := hs.1.symm.trans hs'.1
  rcases H.cases w.frame.fullDim with Hd | Hl | Hl <;>
    rcases H'.cases w'.frame.fullDim with Hd' | Hl' | Hl'
  · obtain ⟨sec₁, hP₁, sec₂, hP₂, hT⟩ := transport_divDiv w.frame.fullDim w'.frame.fullDim H H' ψ
      hWall hA L L' hL Hd Hd' hpass
    exact ⟨sec₁, hP₁, sec₂, hP₂, ψ, hψ, hT⟩
  · exact absurd (hleaf.mpr (leafCover_of_leaf Hl')) (not_leafCover_of_div Hd)
  · exact absurd (hleaf.mpr (leafCover_of_leaf Hl')) (not_leafCover_of_div Hd)
  · exact absurd (hleaf.mp (leafCover_of_leaf Hl)) (not_leafCover_of_div Hd')
  · exact ⟨_, placed_true Hl, _, placed_true Hl', ψ, hψ, transport_leafLeaf w.frame.fullDim
      w'.frame.fullDim H H' ψ hWall hA L L' hL Hl Hl' hpair⟩
  · exact ⟨_, placed_true Hl, _, placed_true Hl', ψ, hψ, transport_leafLeaf w.frame.fullDim
      w'.frame.fullDim H H' ψ hWall hA L L' hL Hl Hl' hpair⟩
  · exact absurd (hleaf.mp (leafCover_of_leaf Hl)) (not_leafCover_of_div Hd')
  · exact ⟨_, placed_true Hl, _, placed_true Hl', ψ, hψ, transport_leafLeaf w.frame.fullDim
      w'.frame.fullDim H H' ψ hWall hA L L' hL Hl Hl' hpair⟩
  · exact ⟨_, placed_true Hl, _, placed_true Hl', ψ, hψ, transport_leafLeaf w.frame.fullDim
      w'.frame.fullDim H H' ψ hWall hA L L' hL Hl Hl' hpair⟩

/-- **Stages 4--5 at valency two, unconditionally at a facet**: two classes of one core at one
labelled metric limit with a valency-two anchor, reading the same split, are equal. -/
theorem splitRigidity {core : Core n p} {y : Fin p → ℚ} {degree : ℕ} (hconn : core.Connected)
    (hn : 3 ≤ n) {e₀ : Fin p} (hy : y e₀ = 0) : ValencyTwoSplit.SplitRigidity core y degree :=
  ValencyTwoSplit.splitRigidity_of_resolutionMatch hconn hn hy (resolutionMatch core y degree)

end Assembly

end DraismaVargas.Count.ValencyTwoResolutionMatch
