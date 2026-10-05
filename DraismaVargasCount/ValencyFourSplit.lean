module

public import DraismaVargasCount.ValencyThreeTypeMatch
public import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent
public import DraismaVargasCount.FacetCensus

@[expose] public section

set_option autoImplicit false

/-!
# The valency-four split, read off an arbitrary incoming cover: `K` as a class invariant

**Source.**  Vargas, Part II (arXiv:2609.09109), the section on changing combinatorial
type: `lemma-above-w0` (rigidity above `w₀`) and the valency-4 limits (Case `{v4-nd4}`:
identity `(□)`, the relabelling `{α,β,γ,δ}`, `|A₊| = |A| - K`, `k₁ = k_α + k_β - 1 - 2K`,
`|A₋| = k_α + k_β - 1 - K`, and the range `0 ≤ K ≤ min(k₂ - 1, |A| - k₅)`).  This is the
valency-four analogue of `ValencyThreeSplit` (`shape`, `existsUnique_reads`,
`split_eq_of_limitIso`) and of `ValencyThreeTypeMatch.type_eq_of_frameIso`, and it feeds
`FacetCensus.MetricCensus`, the census behind the type-change parity (step 3 of
`Assembly`).

## What is proved

* **§1--§2, the shape** (`shape`).  At an incoming cover with `AnchorInput4` (contraction
  forest, four-valent wall, `nd(A) = 4`) the pruned fibre over the anchor is one surviving
  occurrence `e₁` over the contracted target occurrence with two distinct trivalent ends and
  nothing else (`Bridge`), both ends unramified (`ram_eq_zero_of_mem_fib`), each carrying `e₁`
  as its only survivor over the contracted occurrence (`Bridge.ndOver_eq`) and two boundary
  survivors (`Bridge.card_bdAt`), with the local equation `2|X| + 1 = k₁ + Σ k`
  (`Bridge.excess`).  At the limit, `r₀(A) = 0` (`AnchorInput4.ram_zero`) and identity `(□)`
  `Σ k = 2|A| + 2` (`AnchorInput4.square`).  Built on the pruned-fibre census
  `W4IncomingPrunedFibre.AnyWall.census`.
* **§3, the four survivors split `2 + 2`** over the two branch vertices (`labelsAt`,
  `bdAt_eq_image`, `eq_of_mem_ndAt_of_mem_ndAt`: a boundary survivor meets one branch vertex,
  because the contracted occurrence is the only one joining the two endpoints).
* **§4--§5, the reading.**  `Reads4 L (partner, K)`: `partner` is the label at the branch
  vertex `X` of label `0`, and `K = |A| - max(|X|, |Y|)`.  **`existsUnique_reads4`**: relative
  to every labelling exactly one split is read, and it is admissible
  (`valid_of_reads4`: `0 ≤ K ≤ min(k_min - 1, |A| - k_max)`, read off the cover by harmonicity
  at the branch vertices).  **`K_eq_of_reads4`**: `K` does not depend on the labelling.
  `reads4_equations`, `bridge_eq` (`k₁ + 2K + 1 = min(S, Σk - S)`), `sizes_eq`.
* **§6, `K`-rigidity, local form.**  **`reads4_numbers`**: the split and the anchor indices
  determine the bridge index and both branch sizes (`Indices4.bridge`, `sizeZero`,
  `sizeOther`); **`numbers_eq_of_indices_eq`**, **`numbers_eq_of_limitIso`** (two covers,
  labels transported along any geometric isomorphism of limits carrying anchor to anchor).
* **§7--§8, class invariance.**  `reads4_map` and **`split4_eq_of_map`** (the read split is
  invariant under a datum isomorphism carrying the contracted occurrence to the contracted
  occurrence); at regrowths `exists_regrowthAnchor4` (stage 1: the anchor input at every
  facet regrowth of a non-loop slot with a four-valent merged target vertex),
  `eq_anchorOf_of_nd4` / `sourceVertexEquiv_anchorOf4` (the anchor is the limit's only
  `nd = 4` vertex, so limit isomorphisms carry anchor to anchor), **`split4_eq_of_frameIso`**
  and **`K_eq_of_frameIso`** (`K` is a frame-class invariant, for arbitrary labellings).
* **§9, `K` as the census index.**  `V4Limit` (every presenting regrowth, either side, is
  anchored; producer `v4Limit_of_facetPoint`), **`kIndexL` / `kIndexR`** (the index on the
  whole left/right fibres at `m`, of exactly the type `FacetCensus.MetricCensus` asks for;
  `kIndexL_spec`: it is the `K` every presenting regrowth reads under every labelling),
  **`kIndex_admissible`** / `kIndex_admissible_right` / `exists_reference` (on both sides the
  index lies in the admissible range of `m`'s anchor indices), `range_kIndex_eq` (equal
  ranges from per-`K` existence), and the valency-four clause of `MetricCensus`,
  **`metricCensus_clause_of_kIndex`** and **`metricCensus_clause_of_realised`**.
  `regrowth_reads4`: two regrowths over any cores with an isomorphism of limits have
  transported labellings with equal indices, admissible reads, and equal splits give equal
  bridge indices.
* **§10, genus-six data.**  `p1_profile_numbers`: at the genus-six anchor profile
  `(3; 2,2,2,2)` the admissible `K` are `0, 1`, with `(k₁, |X|, |Y|) = (3, 3, 3)` at `K = 0`
  and `(1, 2, 2)` at `K = 1`.

## Tempting inferences, checked

* **The reading matches computed data.**  A computer check of a genus-six `K`-family
  (reading `(|A|; k), |X|, |Y|, k₁` off every class's pruned anchor fibre, near side and both
  Whitehead resolutions) finds every two-class family at `(3; 2,2,2,2)` with
  `(|X|, |Y|, k₁, K) = (3,3,3,0)` and `(2,2,1,1)`; every class satisfies the local equations,
  `(□)`, `|X| + |Y| = |A| + k₁`, `K = |A| - max = min - k₁ = (min S - 1 - k₁)/2` and
  admissibility; `(4; 2,2,2,4)` gives `K = 0` only (range `min(1, 0) = 0`).
* **"`K` is not sheet-independent, so it must be anchored at the bridge sheet"** is an
  artefact of the resolution form.  Read off the pruned anchor fibre,
  `K = |A| - max(|X|,|Y|)` needs neither a sheet nor a labelling (`K_eq_of_reads4`) and is a
  frame-class invariant (`K_eq_of_frameIso`).
* **"The index is `(pairing, K)`"**: **`K` alone is the canonical index.**
  The pairing is defined only relative to a labelling of `m`; it is invariant under frame
  isomorphisms with transported labels (`split4_eq_of_frameIso`), but a label-moving
  automorphism of `m`, where one exists, can move it (as happens at valency three; not
  exhibited at valency four here), so it is not a function on classes without a canonical
  labelling.

## What is NOT proved here -- every hypothesis

* **Injectivity of `kIndexL` / `kIndexR`** (`K`-rigidity in the exhaustion sense: two classes
  of one core at one valency-four metric limit with the same `K` are equal).  What is proved
  here is that the split determines every local number (`reads4_numbers`); injectivity is
  proved in `ValencyFourRigidity` (`kIndexL_injective_of_v4`, `kIndexR_injective_of_v4`).
  The loop merge one might expect to need is vacuous: at a valency-four facet the core never
  has a slot parallel to the vanishing slot (`ValencyFourRigidity.noParallel_of_anchor4`), so
  no two types are ever read over one labelled core.
* **Per-`K` existence on each side** (`hexL`, `hexR` of `metricCensus_clause_of_realised`) is
  not proved here; it is `ValencyFourRealisation.hex_of_resolved`, at every resolved datum,
  on both sides, for all admissible `K`.
* `V4Limit` is produced by `v4Limit_of_facetPoint` modulo the four-valence of each presenting
  regrowth's merged target vertex and the non-loop slot on both cores; it is **not inhabited
  at a concrete regrowth** here.  The `FacetPoint` hypothesis `hpt` is carried by every
  regrowth-level statement (anchor uniqueness uses the single vanishing row).
* New `Prop`s: `AnchorInput4` (see its docstring); `Reads4` (strict: exactly one split,
  `existsUnique_reads4`); `Indices4.Valid`, `Indices4.KAdmissible` (decidable arithmetic;
  strictness `p1_profile_numbers`); `V4Limit` (producer `v4Limit_of_facetPoint`; consumers
  `kIndexL`, `metricCensus_clause_of_realised`).
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

namespace DraismaVargas.Count.ValencyFourSplit

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification
open W4StableSource WallDegeneration FullDimensionalSource PrunedFibreValency PrunedFibreTree
  FullContractionFibre
open ValencyThreeSplit

/-! ## 1.  Labelled survivors at a valency-four anchor, and the anchor indices -/

section Labelling

variable {T : CFGraph} {degree : ℕ} (D : GluingDatum T degree) (A : D.SourceVertex)

/-- **A labelling of the four survivors at a valency-four anchor**: an injective listing of
the surviving occurrences at `A` by `Fin 4`.  No order is imposed (the paper's
`k₂ ≤ k₃ ≤ k₄ ≤ k₅` is a choice made for exposition); every statement below is relative to
the labelling, and a geometric isomorphism of limits transports it (`transport`). -/
structure Labelling4 where
  e : Fin 4 → D.SourceEdge
  mem : ∀ i, e i ∈ ndAt D A
  inj : Function.Injective e

/-- **The anchor indices of a valency-four limit**: the anchor's local degree `|A|` and the
indices of the four labelled survivors. -/
structure Indices4 where
  A : ℕ
  k : Fin 4 → ℕ

/-- **The split read off a valency-four cover**: the label paired with label `0` at one
incoming branch vertex (the base tree `T_S`, `S = {0, partner}`), and the paper's `K`. -/
structure Split4 where
  partner : Fin 4
  K : ℕ

/-- **The admissible splits** (Part II, Case `{v4-nd4}`): `partner ≠ 0` and
`0 ≤ K ≤ min(k_min - 1, |A| - k_max)`, written label by label.  The range does not depend on
the pairing. -/
def Indices4.Valid (a : Indices4) (s : Split4) : Prop :=
  s.partner ≠ 0 ∧ ∀ i, s.K + 1 ≤ a.k i ∧ s.K + a.k i ≤ a.A

namespace Labelling4

variable {D A} (L : Labelling4 D A)

theorem ndAt_eq (hnd : nonDanglingValency D A = 4) :
    ndAt D A = Finset.univ.image L.e := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro f hf
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hf
    exact L.mem i
  · rw [card_ndAt, hnd, Finset.card_image_of_injective _ L.inj]
    simp

theorem sum_ndAt (hnd : nonDanglingValency D A = 4) (f : D.SourceEdge → ℤ) :
    ∑ x ∈ ndAt D A, f x = ∑ i, f (L.e i) := by
  classical
  rw [L.ndAt_eq hnd, Finset.sum_image (fun i _ j _ h ↦ L.inj h)]

/-- The anchor indices of a labelled anchor. -/
def indices : Indices4 where
  A := size D A
  k i := D.sourceEdgeIndex (L.e i)

@[simp] theorem indices_A : L.indices.A = size D A := rfl
@[simp] theorem indices_k (i : Fin 4) : L.indices.k i = D.sourceEdgeIndex (L.e i) := rfl

variable {T₂ : CFGraph} {D₂ : GluingDatum T₂ degree}

/-- **Transport of a labelling along a geometric isomorphism of limits.** -/
def transport (ψ : GeometricDatumIso D D₂) (hConn : D.Connected) :
    Labelling4 D₂ (ψ.sourceVertexEquiv A) where
  e i := ψ.sourceEdgeEquiv (L.e i)
  mem i := by
    have h := (mem_ndAt D _ _).mp (L.mem i)
    rw [mem_ndAt, ψ.isDangling_map_iff hConn, ψ.incident_map_iff]
    exact h
  inj i j h := L.inj (ψ.sourceEdgeEquiv.injective h)

/-- **A geometric isomorphism of limits preserves the anchor indices** of a transported
labelling. -/
theorem indices_transport (ψ : GeometricDatumIso D D₂) (hConn : D.Connected) :
    (L.transport ψ hConn).indices = L.indices := by
  change Indices4.mk _ _ = Indices4.mk _ _
  congr 1
  · exact AnchorLabelling.size_map ψ A
  · funext i
    exact ψ.sourceEdgeIndex_map _

/-- Indices agree along any isomorphism carrying one labelled anchor to another. -/
theorem indices_eq_of_iso {A₂ : D₂.SourceVertex} (L₂ : Labelling4 D₂ A₂)
    (ψ : GeometricDatumIso D D₂) (hψ : ψ.sourceVertexEquiv A = A₂)
    (hL : ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L.e i)) : L₂.indices = L.indices := by
  change Indices4.mk _ _ = Indices4.mk _ _
  congr 1
  · rw [← hψ]; exact AnchorLabelling.size_map ψ A
  · funext i
    rw [hL]
    exact ψ.sourceEdgeIndex_map _

end Labelling4

/-- **A labelling exists** at every anchor of surviving valency four. -/
theorem nonempty_labelling4 (hnd : nonDanglingValency D A = 4) : Nonempty (Labelling4 D A) := by
  classical
  have hcard : (ndAt D A).card = 4 := by rw [card_ndAt, hnd]
  let eqv := (ndAt D A).equivFinOfCardEq hcard
  exact ⟨{ e := fun i ↦ (eqv.symm i).1
           mem := fun i ↦ (eqv.symm i).2
           inj := fun i j h ↦ eqv.symm.injective (Subtype.ext h) }⟩

end Labelling

/-! ## 2.  The anchor input, and the shape of the anchor fibre -/

section Shape

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)

/-- **The inputs of the anchor analysis at one incoming cover of a valency-four wall.**

Interface: exactly the hypotheses of
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_contractionForest` (the `FourStar`
replaced by its defining cardinality, `FourStar.of_card`), at the merged block; every field
is an existing predicate, and at a facet regrowth all three are produced by
`exists_regrowthAnchor4`. -/
structure AnchorInput4 : Prop where
  forest : ContractionForest data a b contracted
  valency : (GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩).card = 4
  nd4 : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4

namespace AnchorInput4

variable {data hc hab hOne block}

theorem compat (H : AnchorInput4 data hc hab hOne block) : DanglingCompatible data hc hab hOne :=
  WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne H.forest

/-- The four-valent wall's star. -/
noncomputable def star (H : AnchorInput4 data hc hab hOne block) :
    W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩ :=
  W4TargetPairings.FourStar.of_card H.valency

/-- Both endpoints of the contracted occurrence carry no target change (`lemma-above-w0` at
`val w₀ = 4`). -/
theorem changeZero (H : AnchorInput4 data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0 :=
  W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne H.star

/-- Both endpoints of the contracted occurrence are trivalent. -/
theorem trivalent (H : AnchorInput4 data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    (GluingDatum.incidentEdges a).card = 3 ∧ (GluingDatum.incidentEdges b).card = 3 := by
  obtain ⟨ha, hb, -, -⟩ := W4Bridge.endpoints_trivalent_of_fourStar data hc hab hOne fd.valid
    fd.changeMinimal H.star
  exact ⟨ha, hb⟩

theorem noGlue (H : AnchorInput4 data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    DanglingEdgeNoGlue (contractDatum data hc hab hOne) :=
  NonTrivalentUniqueFourValent.wall_noGlue data fd hc hab hOne H.forest

/-- `lemma-above-w0` at `val w₀ = 4`: the anchor is unramified. -/
theorem ram_zero (H : AnchorInput4 data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    ram (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 0 :=
  NonTrivalentUniqueFourValent.wall_ramification data fd hc hab hOne H.star H.forest
    (anchorWallBlock (hc := hc) (hab := hab) (hOne := hOne) (block := block))

/-- **Identity `(□)`** (Part II, Case `{v4-nd4}`): at a labelled valency-four anchor the four survivor indices
add up to `2|A| + 2` (the excess formula at ramification zero and surviving valency four). -/
theorem square (H : AnchorInput4 data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (L : Labelling4 (contractDatum data hc hab hOne) (limA data hc hab hOne block)) :
    ∑ i, (L.indices.k i : ℤ) = 2 * (L.indices.A : ℤ) + 2 := by
  have h := ram_eq _ (H.noGlue fd) (limA data hc hab hOne block)
  rw [H.ram_zero fd, H.nd4, L.sum_ndAt H.nd4] at h
  simp only [Labelling4.indices_k, Labelling4.indices_A]
  push_cast at h
  linarith

end AnchorInput4

/-- **The shape of the anchor fibre at a valency-four wall** (Part II, `lemma-above-w0` and
the opening of Case `{v4-nd4}`): the
pruned fibre over the anchor is one surviving occurrence `e₁` over the contracted target
occurrence, with two distinct trivalent ends, and nothing else. -/
structure Bridge where
  e₁ : data.SourceEdge
  intl_eq : intl data hc hab hOne block = {e₁}
  fib_eq : fib data hc hab hOne block = {(data.sourceEnds e₁).1, (data.sourceEnds e₁).2}
  ends_ne : (data.sourceEnds e₁).1 ≠ (data.sourceEnds e₁).2
  nd_fst : nonDanglingValency data (data.sourceEnds e₁).1 = 3
  nd_snd : nonDanglingValency data (data.sourceEnds e₁).2 = 3

variable {data hc hab hOne block}

include fd in
/-- **The shape theorem**: at every incoming cover of a valency-four anchor, the anchor fibre
is a single bridge. -/
theorem shape (H : AnchorInput4 data hc hab hOne block) :
    Nonempty (Bridge data hc hab hOne block) := by
  classical
  have hZero : nonDanglingValency (contractDatum data hc hab hOne)
      (limA data hc hab hOne block) ≠ 0 := by rw [H.nd4]; omega
  have hAccount := sum_nonDanglingValency_activeFibre data hc hab hOne H.compat
    (limA data hc hab hOne block)
  rcases W4IncomingPrunedFibre.AnyWall.census data fd hc hab hOne (H.changeZero fd) _
    (activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne
      H.compat _ hZero) with ⟨point, hPoint, hEmpty⟩ | ⟨edge, hSingleton, hEnds, hNe⟩
  · rw [hPoint, Finset.sum_singleton, hEmpty, Finset.card_empty, H.nd4] at hAccount
    have hPointBound := fd.trivalent point
    omega
  · rw [hEnds, Finset.sum_pair hNe, hSingleton, Finset.card_singleton, H.nd4] at hAccount
    have hLeft := fd.trivalent (data.sourceEnds edge).1
    have hRight := fd.trivalent (data.sourceEnds edge).2
    exact ⟨⟨edge, hSingleton, hEnds, hNe, by omega, by omega⟩⟩

namespace Bridge

variable (P : Bridge data hc hab hOne block)

theorem e₁_mem : P.e₁ ∈ intl data hc hab hOne block := by rw [P.intl_eq]; simp

theorem fst_mem : (data.sourceEnds P.e₁).1 ∈ fib data hc hab hOne block := by
  rw [P.fib_eq]; simp

theorem snd_mem : (data.sourceEnds P.e₁).2 ∈ fib data hc hab hOne block := by
  rw [P.fib_eq]; simp

theorem mem_fib_iff' (X : data.SourceVertex) :
    X ∈ fib data hc hab hOne block ↔
      X = (data.sourceEnds P.e₁).1 ∨ X = (data.sourceEnds P.e₁).2 := by
  rw [P.fib_eq]; simp

theorem e₁_target : P.e₁.1.1 = contracted :=
  (intl_ends data hc hab hOne block P.e₁_mem).2.2.2.2.1

theorem fst_over : (data.sourceEnds P.e₁).1.1.1 = a :=
  (intl_ends data hc hab hOne block P.e₁_mem).2.2.2.2.2.1

theorem snd_over : (data.sourceEnds P.e₁).2.1.1 = b :=
  (intl_ends data hc hab hOne block P.e₁_mem).2.2.2.2.2.2

theorem e₁_survives : ¬ IsDangling data P.e₁ :=
  ((mem_internalEdges data hc hab hOne _ P.e₁).mp P.e₁_mem).1

theorem e₁_mem_ndAt {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    P.e₁ ∈ ndAt data X := by
  rw [mem_ndAt]
  refine ⟨P.e₁_survives, ?_⟩
  rcases (P.mem_fib_iff' X).mp hX with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

include P in
theorem nd_eq_three {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    nonDanglingValency data X = 3 := by
  rcases (P.mem_fib_iff' X).mp hX with rfl | rfl
  exacts [P.nd_fst, P.nd_snd]

end Bridge

theorem over_of_mem_fib {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    X.1.1 = a ∨ X.1.1 = b :=
  ((mem_fib_iff data hc hab hOne block X).mp hX).1

include fd in
/-- A fibre vertex is unramified (`lemma-above-w0`, Case (r0-nd3)). -/
theorem ram_eq_zero_of_mem_fib (H : AnchorInput4 data hc hab hOne block) {X : data.SourceVertex}
    (hX : X ∈ fib data hc hab hOne block) : ram data X = 0 := by
  have hover := over_of_mem_fib hX
  exact W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd X
    (H.changeZero fd _ hover)

namespace Bridge

variable (P : Bridge data hc hab hOne block)

include fd in
/-- At a fibre vertex the bridge is the only surviving occurrence over the contracted target
occurrence. -/
theorem ndOver_eq (H : AnchorInput4 data hc hab hOne block) {X : data.SourceVertex}
    (hX : X ∈ fib data hc hab hOne block) : ndOver data X contracted = {P.e₁} := by
  classical
  ext f
  rw [mem_ndOver, Finset.mem_singleton]
  constructor
  · rintro ⟨hf, hfT⟩
    obtain ⟨hfS, hfI⟩ := (mem_ndAt data X f).mp hf
    obtain ⟨-, heI⟩ := (mem_ndAt data X P.e₁).mp (P.e₁_mem_ndAt hX)
    exact W4IncomingPrunedFibre.AnyWall.contracted_sourceEdge_eq_of_incident data fd hc
      (H.changeZero fd) X f P.e₁ hfT P.e₁_target hfS P.e₁_survives hfI heI
  · rintro rfl
    exact ⟨P.e₁_mem_ndAt hX, P.e₁_target⟩

include fd P in
/-- A fibre vertex carries two boundary survivors. -/
theorem card_bdAt (H : AnchorInput4 data hc hab hOne block) {X : data.SourceVertex}
    (hX : X ∈ fib data hc hab hOne block) : (bdAt data contracted X).card = 2 := by
  have h := card_ndAt_split data (contracted := contracted) X
  rw [P.ndOver_eq fd H hX, Finset.card_singleton, P.nd_eq_three hX] at h
  omega

include fd in
/-- **The local equation at a fibre vertex** (Case (r0-nd3), the non-dangling excess formula
at ramification zero): `2|X| + 1 = k₁ + Σ_{boundary survivors e at X} k(e)`. -/
theorem excess (H : AnchorInput4 data hc hab hOne block) {X : data.SourceVertex}
    (hX : X ∈ fib data hc hab hOne block) :
    2 * (size data X : ℤ) + 1 = data.sourceEdgeIndex P.e₁ +
      ∑ e ∈ bdAt data contracted X, (data.sourceEdgeIndex e : ℤ) := by
  have h := ram_eq data fd.danglingEdgeNoGlue X
  rw [ram_eq_zero_of_mem_fib fd H hX, P.nd_eq_three hX,
    sum_ndAt_split data (contracted := contracted) X, P.ndOver_eq fd H hX,
    Finset.sum_singleton] at h
  push_cast at h
  linarith

end Bridge

end Shape

/-! ## 3.  Lifts of the labelled survivors, and their distribution over the two branch vertices -/

section Lifts

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (L : Labelling4 (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- The incoming boundary occurrence carrying the limit survivor `L.e i`. -/
noncomputable def lift4 (i : Fin 4) : data.SourceEdge :=
  ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)).1

theorem lift4_ne (i : Fin 4) : (lift4 L i).1.1 ≠ contracted :=
  ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)).2

theorem sourceEdgeMap_lift4 (i : Fin 4) :
    sourceEdgeMap data hc hab hOne ⟨lift4 L i, lift4_ne L i⟩ = L.e i :=
  (ContractionFibre.sourceEdgeEquiv data hc hab hOne).apply_symm_apply (L.e i)

theorem index_lift4 (i : Fin 4) :
    data.sourceEdgeIndex (lift4 L i) = L.indices.k i :=
  ContractionFibre.sourceEdgeIndex_symm_sourceEdgeEquiv data hc hab hOne (L.e i)

theorem lift4_injective : Function.Injective (lift4 L) := by
  intro i j h
  apply L.inj
  have h' : ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)) =
      ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e j)) := Subtype.ext h
  exact (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm.injective h'

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A boundary occurrence at a fibre vertex is the lift of a label. -/
theorem exists_lift4_eq (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (limA data hc hab hOne block) = 4)
    {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {e : data.SourceEdge} (he : e ∈ bdAt data contracted X) : ∃ i, lift4 L i = e := by
  classical
  obtain ⟨hnd', hT⟩ := (mem_bdAt data X e).mp he
  obtain ⟨hSurv, hInc⟩ := (mem_ndAt data X e).mp hnd'
  have hmem : sourceEdgeMap data hc hab hOne ⟨e, hT⟩ ∈
      ndAt (contractDatum data hc hab hOne) (limA data hc hab hOne block) := by
    rw [mem_ndAt]
    refine ⟨fun hBad ↦ hSurv (hCompat.2 ⟨e, hT⟩ hBad), ?_⟩
    have hXmap := ((mem_activeFibreVertices data hc hab hOne _ X).mp hX).1
    unfold Incident
    rw [sourceEnds_sourceEdgeMap]
    rcases hInc with h | h
    · left; rw [h]; exact hXmap
    · right; rw [h]; exact hXmap
  rw [L.ndAt_eq hnd] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_⟩
  have h2 : (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i) = ⟨e, hT⟩ := by
    rw [hi]; exact (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm_apply_apply _
  exact congrArg Subtype.val h2

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Every label lifts to a boundary occurrence at some fibre vertex. -/
theorem exists_fib_of_lift4 (hCompat : DanglingCompatible data hc hab hOne) (i : Fin 4) :
    ∃ X ∈ fib data hc hab hOne block, lift4 L i ∈ bdAt data contracted X := by
  classical
  have hm := (mem_ndAt _ _ _).mp (L.mem i)
  rw [← sourceEdgeMap_lift4 L i] at hm
  obtain ⟨hSurv, hInc⟩ := hm
  have hSurv' : ¬ IsDangling data (lift4 L i) := fun hBad ↦
    hSurv (hCompat.1 ⟨_, lift4_ne L i⟩ hBad)
  unfold Incident at hInc
  rw [sourceEnds_sourceEdgeMap] at hInc
  rcases hInc with h | h
  · refine ⟨(data.sourceEnds (lift4 L i)).1, ?_, ?_⟩
    · rw [fib, mem_activeFibreVertices]
      exact ⟨h, ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurv' (Or.inl rfl)⟩
    · exact (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨hSurv', Or.inl rfl⟩, lift4_ne L i⟩
  · refine ⟨(data.sourceEnds (lift4 L i)).2, ?_, ?_⟩
    · rw [fib, mem_activeFibreVertices]
      exact ⟨h, ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurv' (Or.inr rfl)⟩
    · exact (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨hSurv', Or.inr rfl⟩, lift4_ne L i⟩

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- **A boundary occurrence meets at most one fibre vertex**: over one endpoint by
`not_incident_both`, over both endpoints because the contracted occurrence is the only target
occurrence joining them. -/
theorem eq_of_mem_ndAt_of_mem_ndAt {e : data.SourceEdge} (he : e.1.1 ≠ contracted)
    {X Y : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) (heX : e ∈ ndAt data X) (heY : e ∈ ndAt data Y) :
    X = Y := by
  by_contra hXY
  have hIX := ((mem_ndAt data X e).mp heX).2
  have hIY := ((mem_ndAt data Y e).mp heY).2
  rcases over_of_mem_fib hX with hXa | hXb <;> rcases over_of_mem_fib hY with hYa | hYb
  · exact not_incident_both data hXY (hXa.trans hYa.symm) hIX hIY
  · have hta := target_mem_incidentEdges data hIX
    have htb := target_mem_incidentEdges data hIY
    rw [hXa] at hta
    rw [hYb] at htb
    exact not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) hta he htb
  · have hta := target_mem_incidentEdges data hIY
    have htb := target_mem_incidentEdges data hIX
    rw [hYa] at hta
    rw [hXb] at htb
    exact not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) hta he htb
  · exact not_incident_both data hXY (hXb.trans hYb.symm) hIX hIY

/-- The labels whose survivors meet the fibre vertex `X`. -/
noncomputable def labelsAt (X : data.SourceVertex) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun i ↦ lift4 L i ∈ ndAt data X

theorem mem_labelsAt (X : data.SourceVertex) (i : Fin 4) :
    i ∈ labelsAt L X ↔ lift4 L i ∈ ndAt data X := by
  classical
  simp [labelsAt]

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- At a fibre vertex the boundary occurrences are exactly the lifts of its labels. -/
theorem bdAt_eq_image (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (limA data hc hab hOne block) = 4)
    {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    bdAt data contracted X = (labelsAt L X).image (lift4 L) := by
  classical
  ext e
  rw [Finset.mem_image]
  constructor
  · intro he
    obtain ⟨i, rfl⟩ := exists_lift4_eq L hCompat hnd hX he
    exact ⟨i, (mem_labelsAt L X i).mpr ((mem_bdAt data X _).mp he).1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact (mem_bdAt data X _).mpr ⟨(mem_labelsAt L X i).mp hi, lift4_ne L i⟩

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem sum_bdAt (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (limA data hc hab hOne block) = 4)
    {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    ∑ e ∈ bdAt data contracted X, (data.sourceEdgeIndex e : ℤ) =
      ∑ i ∈ labelsAt L X, (L.indices.k i : ℤ) := by
  classical
  rw [bdAt_eq_image L hCompat hnd hX, Finset.sum_image (fun i _ j _ h ↦ lift4_injective L h)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [index_lift4]

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem card_labelsAt (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (limA data hc hab hOne block) = 4)
    {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    (labelsAt L X).card = (bdAt data contracted X).card := by
  classical
  rw [bdAt_eq_image L hCompat hnd hX, Finset.card_image_of_injective _ (lift4_injective L)]

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Two fibre vertices sharing a label are equal. -/
theorem eq_of_mem_labelsAt {X Y : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) {i : Fin 4} (hiX : i ∈ labelsAt L X)
    (hiY : i ∈ labelsAt L Y) : X = Y :=
  eq_of_mem_ndAt_of_mem_ndAt (lift4_ne L i) hX hY ((mem_labelsAt L X i).mp hiX)
    ((mem_labelsAt L Y i).mp hiY)

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Every label meets some fibre vertex. -/
theorem exists_mem_labelsAt (hCompat : DanglingCompatible data hc hab hOne) (i : Fin 4) :
    ∃ X ∈ fib data hc hab hOne block, i ∈ labelsAt L X := by
  obtain ⟨X, hX, hi⟩ := exists_fib_of_lift4 L hCompat i
  exact ⟨X, hX, (mem_labelsAt L X i).mpr ((mem_bdAt data X _).mp hi).1⟩

end Lifts

/-! ## 4.  Reading `(pairing, K)` off the cover, and the local equations -/

section Reading

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (L : Labelling4 (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- **The split an incoming cover realises** (Part II, Case `{v4-nd4}`), read off its anchor fibre
relative to a labelling `L` of the limit's survivors: `partner` is the label whose survivor
meets the same incoming branch vertex `X` as label `0` (the base tree `T_S`, `S = {0, partner}`),
and `K = |A| - max(|X|, |Y|)` with `Y` the other branch vertex (the paper's
`|A₊| = |A| - K`, `A₊` the larger of the two).

This is the pruned-fibre form of `K`: it counts the sheets of the two *branch* vertices, not
the blocks of a resolution at a chosen sheet, so it does not depend on a sheet (contrast the
resolution form, whose `blockCountWithin` count is sheet-dependent) and it does not depend on
`L` either
(`K_eq_of_reads4`). -/
def Reads4 (s : Split4) : Prop :=
  s.partner ≠ 0 ∧ ∃ X ∈ fib data hc hab hOne block, ∃ Y ∈ fib data hc hab hOne block, X ≠ Y ∧
    0 ∈ labelsAt L X ∧ s.partner ∈ labelsAt L X ∧
    s.K + max (size data X) (size data Y) = anchorSize data block

variable {L}

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The anchor size is the limit anchor's local degree. -/
theorem anchorSize_eq : anchorSize data block = L.indices.A :=
  (size_limA data hc hab hOne block).symm

include fd in
/-- **The two labels at a branch vertex**: every branch vertex carries exactly two labels, and
the excess formula there reads `2|Z| + 1 = k₁ + k_i + k_j`. -/
theorem labels_at (H : AnchorInput4 data hc hab hOne block) (P : Bridge data hc hab hOne block)
    {Z : data.SourceVertex} (hZ : Z ∈ fib data hc hab hOne block) {i : Fin 4}
    (hi : i ∈ labelsAt L Z) :
    ∃ j, j ≠ i ∧ labelsAt L Z = {i, j} ∧
      2 * size data Z + 1 = data.sourceEdgeIndex P.e₁ + L.indices.k i + L.indices.k j := by
  classical
  have hcard : (labelsAt L Z).card = 2 := by
    rw [card_labelsAt L H.compat H.nd4 hZ, P.card_bdAt fd H hZ]
  obtain ⟨x, y, hxy, hxyEq⟩ := Finset.card_eq_two.mp hcard
  have hex := P.excess fd H hZ
  rw [sum_bdAt L H.compat H.nd4 hZ, hxyEq, Finset.sum_pair hxy] at hex
  rw [hxyEq] at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · refine ⟨y, hxy.symm, hxyEq, ?_⟩
    omega
  · refine ⟨x, hxy, ?_, ?_⟩
    · rw [hxyEq, Finset.pair_comm]
    · omega

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- A label at a branch vertex has index at most its size. -/
theorem index_le_size_of_mem {Z : data.SourceVertex} {i : Fin 4} (hi : i ∈ labelsAt L Z) :
    L.indices.k i ≤ size data Z := by
  have h := index_le_size data ((mem_labelsAt L Z i).mp hi)
  rw [index_lift4] at h
  exact_mod_cast h

include fd in
/-- **The two branch vertices share out the four labels.** -/
theorem sum_labels (H : AnchorInput4 data hc hab hOne block)
    {X Y : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) (hXY : X ≠ Y) :
    ∑ i ∈ labelsAt L X, L.indices.k i + ∑ i ∈ labelsAt L Y, L.indices.k i =
      ∑ i, L.indices.k i := by
  classical
  have hdisj : Disjoint (labelsAt L X) (labelsAt L Y) := by
    rw [Finset.disjoint_left]
    intro i hiX hiY
    exact hXY (eq_of_mem_labelsAt L hX hY hiX hiY)
  have hunion : labelsAt L X ∪ labelsAt L Y = Finset.univ := by
    obtain ⟨P⟩ := shape fd H
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨Z, hZ, hi⟩ := exists_mem_labelsAt L H.compat i
    rw [Finset.mem_union]
    rcases (P.mem_fib_iff' Z).mp hZ with rfl | rfl <;>
      rcases (P.mem_fib_iff' X).mp hX with rfl | rfl <;>
      rcases (P.mem_fib_iff' Y).mp hY with rfl | rfl <;>
      first | exact Or.inl hi | exact Or.inr hi | exact absurd rfl hXY
  rw [← Finset.sum_union hdisj, hunion]

/-- The total of the four indices. -/
def Indices4.total (a : Indices4) : ℕ := ∑ i, a.k i

include fd in
/-- **The local equations of a read split** (Part II, Case `{v4-nd4}`): with `X` the branch vertex of
labels `0` and `partner` and `Y` the other one,
`2|X| + 1 = k₁ + k₀ + k_partner`, `2|Y| + 1 = k₁ + (Σk - k₀ - k_partner)`,
`Σk = 2|A| + 2` (identity `(□)`), `|X| + |Y| = |A| + k₁`, and `K + max(|X|,|Y|) = |A|`. -/
theorem reads4_equations (H : AnchorInput4 data hc hab hOne block)
    (P : Bridge data hc hab hOne block) {s : Split4} (hs : Reads4 L s) :
    ∃ X ∈ fib data hc hab hOne block, ∃ Y ∈ fib data hc hab hOne block, X ≠ Y ∧
      labelsAt L X = {0, s.partner} ∧
      2 * size data X + 1 = data.sourceEdgeIndex P.e₁ + L.indices.k 0 + L.indices.k s.partner ∧
      2 * size data Y + 1 + L.indices.k 0 + L.indices.k s.partner =
        data.sourceEdgeIndex P.e₁ + L.indices.total ∧
      L.indices.total = 2 * L.indices.A + 2 ∧
      size data X + size data Y = L.indices.A + data.sourceEdgeIndex P.e₁ ∧
      s.K + max (size data X) (size data Y) = L.indices.A := by
  classical
  obtain ⟨hp, X, hX, Y, hY, hXY, h0, hpX, hK⟩ := hs
  obtain ⟨j, hj0, hXeq, hXex⟩ := labels_at fd H P hX h0
  have hjp : j = s.partner := by
    rw [hXeq] at hpX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpX
    rcases hpX with h | h
    · exact absurd h hp
    · exact h.symm
  subst hjp
  -- the other vertex
  obtain ⟨l, hlY⟩ : (labelsAt L Y).Nonempty := by
    rw [← Finset.card_pos, card_labelsAt L H.compat H.nd4 hY, P.card_bdAt fd H hY]
    omega
  obtain ⟨m, -, hYeq, hYex⟩ := labels_at fd H P hY hlY
  have hsum := sum_labels fd (L := L) H hX hY hXY
  have hsq := H.square fd L
  have hne0 : (0 : Fin 4) ≠ s.partner := hj0.symm
  rw [hXeq, Finset.sum_pair hne0] at hsum
  have hlm : l ≠ m := by
    intro h
    have hc2 : (labelsAt L Y).card = 2 := by
      rw [card_labelsAt L H.compat H.nd4 hY, P.card_bdAt fd H hY]
    rw [hYeq, h, Finset.pair_eq_singleton, Finset.card_singleton] at hc2
    omega
  rw [hYeq, Finset.sum_pair hlm] at hsum
  have htot : L.indices.total = ∑ i, L.indices.k i := rfl
  have hsq' : L.indices.total = 2 * L.indices.A + 2 := by
    rw [htot]
    have : ((∑ i, L.indices.k i : ℕ) : ℤ) = 2 * (L.indices.A : ℤ) + 2 := by
      push_cast; exact hsq
    exact_mod_cast this
  rw [anchorSize_eq (L := L)] at hK
  refine ⟨X, hX, Y, hY, hXY, hXeq, hXex, by omega, hsq', by omega, hK⟩

end Reading

/-! ## 5.  Existence, uniqueness and admissibility of the read split; `K` is labelling-free -/

section Determination

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Two distinct branch vertices exhaust the fibre. -/
theorem eq_or_eq_of_mem_fib (P : Bridge data hc hab hOne block)
    {X Y Z : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) (hXY : X ≠ Y)
    (hZ : Z ∈ fib data hc hab hOne block) : Z = X ∨ Z = Y := by
  rcases (P.mem_fib_iff' Z).mp hZ with rfl | rfl <;>
    rcases (P.mem_fib_iff' X).mp hX with rfl | rfl <;>
    rcases (P.mem_fib_iff' Y).mp hY with rfl | rfl <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hXY

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The other branch vertex. -/
theorem exists_other (P : Bridge data hc hab hOne block) {X : data.SourceVertex}
    (hX : X ∈ fib data hc hab hOne block) :
    ∃ Y ∈ fib data hc hab hOne block, X ≠ Y := by
  rcases (P.mem_fib_iff' X).mp hX with rfl | rfl
  · exact ⟨_, P.snd_mem, P.ends_ne⟩
  · exact ⟨_, P.fst_mem, P.ends_ne.symm⟩

variable (L : Labelling4 (contractDatum data hc hab hOne) (limA data hc hab hOne block))

include fd in
/-- **Every read split is admissible**: `0 ≤ K ≤ min(k_min - 1, |A| - k_max)` (Part II, Case `{v4-nd4}`).
Both bounds are read off the cover: `|A₋| ≥ k` at each branch vertex (harmonicity) and the
two local equations. -/
theorem valid_of_reads4 (H : AnchorInput4 data hc hab hOne block) {s : Split4}
    (hs : Reads4 L s) : L.indices.Valid s := by
  classical
  obtain ⟨P⟩ := shape fd H
  have hp := hs.1
  obtain ⟨X, hX, Y, hY, hXY, -, -, -, -, hsum, hK⟩ := reads4_equations fd H P hs
  refine ⟨hp, fun i ↦ ?_⟩
  obtain ⟨Z, hZ, hi⟩ := exists_mem_labelsAt L H.compat i
  obtain ⟨j, -, hZeq, hZex⟩ := labels_at fd H P hZ hi
  have hj : j ∈ labelsAt L Z := by rw [hZeq]; simp
  have hki := index_le_size_of_mem hi
  have hkj := index_le_size_of_mem hj
  rcases eq_or_eq_of_mem_fib P hX hY hXY hZ with rfl | rfl <;> omega

include fd in
/-- **Stages 1 and 2 at valency four: the split of an arbitrary incoming cover.**  At every
incoming cover of a valency-four anchor, relative to any labelling `L` of the limit's
survivors, exactly one split `(partner, K)` is read off the cover, and it is admissible for the
limit's anchor indices. -/
theorem existsUnique_reads4 (H : AnchorInput4 data hc hab hOne block) :
    ∃ s : Split4, Reads4 L s ∧ L.indices.Valid s ∧ ∀ s', Reads4 L s' → s' = s := by
  classical
  obtain ⟨P⟩ := shape fd H
  obtain ⟨X, hX, h0⟩ := exists_mem_labelsAt L H.compat 0
  obtain ⟨j, hj0, hXeq, -⟩ := labels_at fd H P hX h0
  obtain ⟨Y, hY, hXY⟩ := exists_other P hX
  have hjX : j ∈ labelsAt L X := by rw [hXeq]; simp
  have hle : max (size data X) (size data Y) ≤ anchorSize data block :=
    max_le (size_le_anchorSize data hc hab hOne block hX)
      (size_le_anchorSize data hc hab hOne block hY)
  let s : Split4 := ⟨j, anchorSize data block - max (size data X) (size data Y)⟩
  have hs : Reads4 L s := ⟨hj0, X, hX, Y, hY, hXY, h0, hjX, by simp only [s]; omega⟩
  refine ⟨s, hs, valid_of_reads4 fd L H hs, fun s' hs' ↦ ?_⟩
  obtain ⟨hp', X', hX', Y', hY', hXY', h0', hpX', hK'⟩ := hs'
  have hXX : X' = X := eq_of_mem_labelsAt L hX' hX h0' h0
  subst hXX
  have hYY : Y' = Y := by
    rcases eq_or_eq_of_mem_fib P hX' hY hXY hY' with h | h
    · exact absurd h.symm hXY'
    · exact h
  subst hYY
  have hpp : s'.partner = j := by
    rw [hXeq] at hpX'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpX'
    rcases hpX' with h | h
    · exact absurd h hp'
    · exact h
  cases s'
  simp only [s, Split4.mk.injEq] at hpp hK' ⊢
  exact ⟨hpp, by omega⟩

include fd in
/-- **`K` does not depend on the labelling**: two labellings of one anchor read the same `K`
off one cover (only the partner label can move). -/
theorem K_eq_of_reads4 (H : AnchorInput4 data hc hab hOne block)
    (L' : Labelling4 (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    {s s' : Split4} (hs : Reads4 L s) (hs' : Reads4 L' s') : s.K = s'.K := by
  classical
  obtain ⟨P⟩ := shape fd H
  obtain ⟨-, X, hX, Y, hY, hXY, -, -, hK⟩ := hs
  obtain ⟨-, X', hX', Y', hY', hXY', -, -, hK'⟩ := hs'
  rcases eq_or_eq_of_mem_fib P hX hY hXY hX' with rfl | rfl <;>
    rcases eq_or_eq_of_mem_fib P hX hY hXY hY' with rfl | rfl
  · exact absurd rfl hXY'
  · omega
  · rw [max_comm] at hK'; omega
  · exact absurd rfl hXY'

include fd in
/-- **The bridge index of a read split** (Part II, Case `{v4-nd4}`): `k₁ + 2K + 1 = min(S, Σk - S)`, with
`S = k₀ + k_partner` the index sum at the branch vertex of label `0` -- the paper's
`k₁ = k_α + k_β - 1 - 2K`, `k_α + k_β` the smaller of the two side sums. -/
theorem bridge_eq (H : AnchorInput4 data hc hab hOne block) (P : Bridge data hc hab hOne block)
    {s : Split4} (hs : Reads4 L s) :
    data.sourceEdgeIndex P.e₁ + 2 * s.K + 1 =
      min (L.indices.k 0 + L.indices.k s.partner)
        (L.indices.total - (L.indices.k 0 + L.indices.k s.partner)) := by
  obtain ⟨X, -, Y, -, -, -, hXex, hYex, hsq, hXY, hK⟩ := reads4_equations fd H P hs
  omega

include fd in
/-- **The branch sizes of a read split** (Part II, Case `{v4-nd4}`): the branch vertex of label `0` has
`2|X| + 1 = k₁ + S`, the other `2|Y| + 1 = k₁ + (Σk - S)`, and the larger one has size
`|A| - K`. -/
theorem sizes_eq (H : AnchorInput4 data hc hab hOne block) (P : Bridge data hc hab hOne block)
    {s : Split4} (hs : Reads4 L s) :
    ∃ X ∈ fib data hc hab hOne block, ∃ Y ∈ fib data hc hab hOne block, X ≠ Y ∧
      0 ∈ labelsAt L X ∧ s.partner ∈ labelsAt L X ∧
      2 * size data X + 1 = data.sourceEdgeIndex P.e₁ + (L.indices.k 0 + L.indices.k s.partner) ∧
      2 * size data Y + 1 = data.sourceEdgeIndex P.e₁ +
        (L.indices.total - (L.indices.k 0 + L.indices.k s.partner)) ∧
      max (size data X) (size data Y) + s.K = L.indices.A := by
  obtain ⟨X, hX, Y, hY, hXY, hXeq, hXex, hYex, hsq, hXYs, hK⟩ := reads4_equations fd H P hs
  refine ⟨X, hX, Y, hY, hXY, by rw [hXeq]; simp, by rw [hXeq]; simp, by omega, by omega,
    by omega⟩

end Determination

/-! ## 6.  `K`-rigidity: the split determines the local numbers -/

section Numbers

/-- The index sum at the branch vertex of label `0`. -/
def Indices4.side (a : Indices4) (s : Split4) : ℕ := a.k 0 + a.k s.partner

/-- **The bridge index a split prescribes** (Part II, Case `{v4-nd4}`): `k₁ = min(S, Σk - S) - 1 - 2K`. -/
def Indices4.bridge (a : Indices4) (s : Split4) : ℕ :=
  min (a.side s) (a.total - a.side s) - 1 - 2 * s.K

/-- **The size of the branch vertex of label `0`** a split prescribes: `(k₁ + S - 1) / 2`. -/
def Indices4.sizeZero (a : Indices4) (s : Split4) : ℕ := (a.bridge s + a.side s - 1) / 2

/-- **The size of the other branch vertex** a split prescribes: `(k₁ + Σk - S - 1) / 2`. -/
def Indices4.sizeOther (a : Indices4) (s : Split4) : ℕ :=
  (a.bridge s + (a.total - a.side s) - 1) / 2

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (L : Labelling4 (contractDatum data hc hab hOne) (limA data hc hab hOne block))

include fd in
/-- **`K`-rigidity, local form.**  The read split `(partner, K)` and the limit's anchor indices
determine the whole local picture over the anchor: the bridge index `k₁`, and the sizes of the
two branch vertices (the one carrying label `0`, and the other).  This is the valency-four
analogue of `ValencyThreeSplit.split_eq_of_indices_eq`: at valency three the type alone
determines the split; at valency four the type and `K` do (as Part II puts it, fixing `K`
determines the sizes). -/
theorem reads4_numbers (H : AnchorInput4 data hc hab hOne block)
    (P : Bridge data hc hab hOne block) {s : Split4} (hs : Reads4 L s) :
    data.sourceEdgeIndex P.e₁ = L.indices.bridge s ∧
      ∃ X ∈ fib data hc hab hOne block, ∃ Y ∈ fib data hc hab hOne block, X ≠ Y ∧
        0 ∈ labelsAt L X ∧ s.partner ∈ labelsAt L X ∧
        size data X = L.indices.sizeZero s ∧ size data Y = L.indices.sizeOther s := by
  have hb := bridge_eq fd L H P hs
  obtain ⟨X, hX, Y, hY, hXY, h0, hp, hXe, hYe, -⟩ := sizes_eq fd L H P hs
  have hbr : data.sourceEdgeIndex P.e₁ = L.indices.bridge s := by
    unfold Indices4.bridge Indices4.side
    omega
  refine ⟨hbr, X, hX, Y, hY, hXY, h0, hp, ?_, ?_⟩
  · unfold Indices4.sizeZero
    rw [← hbr]
    unfold Indices4.side
    omega
  · unfold Indices4.sizeOther
    rw [← hbr]
    unfold Indices4.side
    omega

end Numbers

section TwoCovers

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

include fd₁ fd₂ in
/-- **`K`-rigidity across two covers.**  Two incoming covers of valency-four anchors whose
labelled limits have the same anchor indices, reading the same split `(partner, K)`, have the
same bridge index and the same branch sizes (the vertex carrying label `0`, and the other). -/
theorem numbers_eq_of_indices_eq (H₁ : AnchorInput4 data₁ hc₁ hab₁ hOne₁ block₁)
    (H₂ : AnchorInput4 data₂ hc₂ hab₂ hOne₂ block₂)
    (P₁ : Bridge data₁ hc₁ hab₁ hOne₁ block₁) (P₂ : Bridge data₂ hc₂ hab₂ hOne₂ block₂)
    (L₁ : Labelling4 (contractDatum data₁ hc₁ hab₁ hOne₁) (limA data₁ hc₁ hab₁ hOne₁ block₁))
    (L₂ : Labelling4 (contractDatum data₂ hc₂ hab₂ hOne₂) (limA data₂ hc₂ hab₂ hOne₂ block₂))
    (hidx : L₁.indices = L₂.indices) {s : Split4} (h₁ : Reads4 L₁ s) (h₂ : Reads4 L₂ s) :
    data₁.sourceEdgeIndex P₁.e₁ = data₂.sourceEdgeIndex P₂.e₁ ∧
      ∃ X₁ Y₁ X₂ Y₂, X₁ ∈ fib data₁ hc₁ hab₁ hOne₁ block₁ ∧ Y₁ ∈ fib data₁ hc₁ hab₁ hOne₁ block₁ ∧
        X₂ ∈ fib data₂ hc₂ hab₂ hOne₂ block₂ ∧ Y₂ ∈ fib data₂ hc₂ hab₂ hOne₂ block₂ ∧
        X₁ ≠ Y₁ ∧ X₂ ≠ Y₂ ∧ 0 ∈ labelsAt L₁ X₁ ∧ 0 ∈ labelsAt L₂ X₂ ∧
        size data₁ X₁ = size data₂ X₂ ∧ size data₁ Y₁ = size data₂ Y₂ := by
  obtain ⟨hb₁, X₁, hX₁, Y₁, hY₁, hXY₁, h0₁, -, hsX₁, hsY₁⟩ := reads4_numbers fd₁ L₁ H₁ P₁ h₁
  obtain ⟨hb₂, X₂, hX₂, Y₂, hY₂, hXY₂, h0₂, -, hsX₂, hsY₂⟩ := reads4_numbers fd₂ L₂ H₂ P₂ h₂
  rw [hidx] at hb₁ hsX₁ hsY₁
  exact ⟨hb₁.trans hb₂.symm, X₁, Y₁, X₂, Y₂, hX₁, hY₁, hX₂, hY₂, hXY₁, hXY₂, h0₁, h0₂,
    hsX₁.trans hsX₂.symm, hsY₁.trans hsY₂.symm⟩

include fd₁ fd₂ in
/-- **`K`-rigidity along an isomorphism of limits**: labels transported along a geometric
isomorphism of the two limits carrying anchor to anchor give equal anchor indices, hence equal
local numbers for equal read splits.  (The valency-four analogue of
`ValencyThreeSplit.split_eq_of_limitIso`.) -/
theorem numbers_eq_of_limitIso (H₁ : AnchorInput4 data₁ hc₁ hab₁ hOne₁ block₁)
    (H₂ : AnchorInput4 data₂ hc₂ hab₂ hOne₂ block₂)
    (P₁ : Bridge data₁ hc₁ hab₁ hOne₁ block₁) (P₂ : Bridge data₂ hc₂ hab₂ hOne₂ block₂)
    (ψ : GeometricDatumIso (contractDatum data₁ hc₁ hab₁ hOne₁)
      (contractDatum data₂ hc₂ hab₂ hOne₂))
    (hψ : ψ.sourceVertexEquiv (limA data₁ hc₁ hab₁ hOne₁ block₁) =
      limA data₂ hc₂ hab₂ hOne₂ block₂)
    (L₁ : Labelling4 (contractDatum data₁ hc₁ hab₁ hOne₁) (limA data₁ hc₁ hab₁ hOne₁ block₁))
    (L₂ : Labelling4 (contractDatum data₂ hc₂ hab₂ hOne₂) (limA data₂ hc₂ hab₂ hOne₂ block₂))
    (hL : ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i)) {s : Split4} (h₁ : Reads4 L₁ s)
    (h₂ : Reads4 L₂ s) :
    data₁.sourceEdgeIndex P₁.e₁ = data₂.sourceEdgeIndex P₂.e₁ ∧
      ∃ X₁ Y₁ X₂ Y₂, X₁ ∈ fib data₁ hc₁ hab₁ hOne₁ block₁ ∧ Y₁ ∈ fib data₁ hc₁ hab₁ hOne₁ block₁ ∧
        X₂ ∈ fib data₂ hc₂ hab₂ hOne₂ block₂ ∧ Y₂ ∈ fib data₂ hc₂ hab₂ hOne₂ block₂ ∧
        X₁ ≠ Y₁ ∧ X₂ ≠ Y₂ ∧ 0 ∈ labelsAt L₁ X₁ ∧ 0 ∈ labelsAt L₂ X₂ ∧
        size data₁ X₁ = size data₂ X₂ ∧ size data₁ Y₁ = size data₂ Y₂ :=
  numbers_eq_of_indices_eq fd₁ fd₂ H₁ H₂ P₁ P₂ L₁ L₂
    (L₁.indices_eq_of_iso L₂ ψ hψ hL).symm h₁ h₂

end TwoCovers

/-! ## 7.  The read split is transported: `K` and the pairing are class invariants -/

section Transport

open ValencyThreeTypeMatch (contractIso sourceEdgeMap_comm targetEdge_ne HasOtherEdge
  hasOtherEdge_of_two_le fib_map ndAt_map)

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ}
  {D₁ : GluingDatum target₁ degree} {D₂ : GluingDatum target₂ degree}
  (ι : GeometricDatumIso D₁ D₂) (c₁ : target₁.edges)
  (hOne₁ : num_edges target₁ (c₁ : target₁.V × target₁.V).1 (c₁ : target₁.V × target₁.V).2 = 1)
  (hOne₂ : num_edges target₂ (ι.targetEdge c₁ : target₂.V × target₂.V).1
    (ι.targetEdge c₁ : target₂.V × target₂.V).2 = 1)
  (hConn : D₁.Connected)
  (hEnds : HasOtherEdge c₁ (c₁ : target₁.V × target₁.V).1 ∧
    HasOtherEdge c₁ (c₁ : target₁.V × target₁.V).2)
  {block₁ : (mergedPartition D₁ (c₁ : target₁.V × target₁.V).1
    (c₁ : target₁.V × target₁.V).2).Blocks}
  {block₂ : (mergedPartition D₂ (ι.targetEdge c₁ : target₂.V × target₂.V).1
    (ι.targetEdge c₁ : target₂.V × target₂.V).2).Blocks}
  (hA : (contractIso ι c₁ hOne₁ hOne₂).sourceVertexEquiv (limA D₁ rfl (fst_ne_snd c₁) hOne₁ block₁) =
    limA D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ block₂)
  (L₁ : Labelling4 (contractDatum D₁ rfl (fst_ne_snd c₁) hOne₁)
    (limA D₁ rfl (fst_ne_snd c₁) hOne₁ block₁))
  (L₂ : Labelling4 (contractDatum D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂)
    (limA D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ block₂))
  (hL : ∀ i, L₂.e i = (contractIso ι c₁ hOne₁ hOne₂).sourceEdgeEquiv (L₁.e i))

include hL in
/-- **Lifts of transported labels are transported lifts.** -/
theorem lift4_map (i : Fin 4) : lift4 L₂ i = ι.sourceEdgeEquiv (lift4 L₁ i) := by
  have h := sourceEdgeMap_comm ι c₁ hOne₁ hOne₂ ⟨lift4 L₁ i, lift4_ne L₁ i⟩
  have h2 : sourceEdgeMap D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ ⟨lift4 L₂ i, lift4_ne L₂ i⟩ =
      sourceEdgeMap D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂
        ⟨ι.sourceEdgeEquiv (lift4 L₁ i), targetEdge_ne ι c₁ (lift4_ne L₁ i)⟩ := by
    rw [sourceEdgeMap_lift4, hL, ← h, sourceEdgeMap_lift4]
  exact congrArg Subtype.val (sourceEdgeMap_injective _ _ _ _ h2)

include hConn hL in
theorem labelsAt_map {X : D₁.SourceVertex} {i : Fin 4} (hi : i ∈ labelsAt L₁ X) :
    i ∈ labelsAt L₂ (ι.sourceVertexEquiv X) := by
  rw [mem_labelsAt] at hi ⊢
  rw [lift4_map ι c₁ hOne₁ hOne₂ L₁ L₂ hL]
  exact ndAt_map ι hConn hi

include hA in
/-- The anchor size is transported. -/
theorem anchorSize_map :
    anchorSize D₂ block₂ = anchorSize D₁ block₁ := by
  rw [← size_limA, ← size_limA, ← hA]
  exact AnchorLabelling.size_map _ _

include hConn hEnds hA hL in
/-- **The read split is transported** along a geometric datum isomorphism carrying the
contracted occurrence to the contracted occurrence, for labellings transported along the
induced isomorphism of limits. -/
theorem reads4_map {s : Split4} (hs : Reads4 L₁ s) : Reads4 L₂ s := by
  obtain ⟨hp, X, hX, Y, hY, hXY, h0, hpX, hK⟩ := hs
  refine ⟨hp, ι.sourceVertexEquiv X, fib_map ι c₁ hOne₁ hOne₂ hConn hEnds hA hX,
    ι.sourceVertexEquiv Y, fib_map ι c₁ hOne₁ hOne₂ hConn hEnds hA hY,
    fun h ↦ hXY (ι.sourceVertexEquiv.injective h),
    labelsAt_map ι c₁ hOne₁ hOne₂ hConn L₁ L₂ hL h0,
    labelsAt_map ι c₁ hOne₁ hOne₂ hConn L₁ L₂ hL hpX, ?_⟩
  rw [AnchorLabelling.size_map, AnchorLabelling.size_map,
    anchorSize_map ι c₁ hOne₁ hOne₂ hA]
  exact hK

end Transport

section Invariance

open ValencyThreeTypeMatch (HasOtherEdge hasOtherEdge_of_two_le)

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {D₁ : GluingDatum target₁ degree} {D₂ : GluingDatum target₂ degree}

/-- At a valency-four anchor both endpoints of the contracted occurrence carry another
occurrence (both are trivalent). -/
theorem hasOtherEdge_of_anchorInput4 (fd : FullDimensionalSourcePresentation D₁ coordinate)
    {c : target₁.edges}
    {hOne : num_edges target₁ (c : target₁.V × target₁.V).1 (c : target₁.V × target₁.V).2 = 1}
    {block : (mergedPartition D₁ (c : target₁.V × target₁.V).1
      (c : target₁.V × target₁.V).2).Blocks}
    (H : AnchorInput4 D₁ rfl (fst_ne_snd c) hOne block) :
    HasOtherEdge c (c : target₁.V × target₁.V).1 ∧ HasOtherEdge c (c : target₁.V × target₁.V).2 := by
  obtain ⟨ha, hb⟩ := H.trivalent fd
  exact ⟨hasOtherEdge_of_two_le c _ (by rw [ha]; omega),
    hasOtherEdge_of_two_le c _ (by rw [hb]; omega)⟩

/-- **The read split is invariant under a datum isomorphism carrying the contracted
occurrence to the contracted occurrence**, for labellings transported along the induced
contraction isomorphism: same partner, same `K`.  Stated for an arbitrary name `c₂` of the
image occurrence. -/
theorem split4_eq_of_map (fd₁ : FullDimensionalSourcePresentation D₁ coordinate)
    (fd₂ : FullDimensionalSourcePresentation D₂ coordinate)
    (ι : GeometricDatumIso D₁ D₂) (c₁ : target₁.edges) (c₂ : target₂.edges)
    (h : ι.targetEdge c₁ = c₂)
    (hOne₁ : num_edges target₁ (c₁ : target₁.V × target₁.V).1 (c₁ : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (c₂ : target₂.V × target₂.V).1 (c₂ : target₂.V × target₂.V).2 = 1)
    {block₁ : (mergedPartition D₁ (c₁ : target₁.V × target₁.V).1
      (c₁ : target₁.V × target₁.V).2).Blocks}
    {block₂ : (mergedPartition D₂ (c₂ : target₂.V × target₂.V).1
      (c₂ : target₂.V × target₂.V).2).Blocks}
    (H₁ : AnchorInput4 D₁ rfl (fst_ne_snd c₁) hOne₁ block₁)
    (H₂ : AnchorInput4 D₂ rfl (fst_ne_snd c₂) hOne₂ block₂)
    (hA : (GeometricLimitTransport.contractDatumIsoOfEdgeEq ι c₁ c₂ h hOne₁ hOne₂).sourceVertexEquiv
      (limA D₁ rfl (fst_ne_snd c₁) hOne₁ block₁) = limA D₂ rfl (fst_ne_snd c₂) hOne₂ block₂)
    (L₁ : Labelling4 (contractDatum D₁ rfl (fst_ne_snd c₁) hOne₁)
      (limA D₁ rfl (fst_ne_snd c₁) hOne₁ block₁))
    (L₂ : Labelling4 (contractDatum D₂ rfl (fst_ne_snd c₂) hOne₂)
      (limA D₂ rfl (fst_ne_snd c₂) hOne₂ block₂))
    (hL : ∀ i, L₂.e i =
      (GeometricLimitTransport.contractDatumIsoOfEdgeEq ι c₁ c₂ h hOne₁ hOne₂).sourceEdgeEquiv
        (L₁.e i))
    {s₁ s₂ : Split4} (hs₁ : Reads4 L₁ s₁) (hs₂ : Reads4 L₂ s₂) : s₁ = s₂ := by
  subst h
  have hs₁' := reads4_map ι c₁ hOne₁ hOne₂ fd₁.valid.1 (hasOtherEdge_of_anchorInput4 fd₁ H₁) hA
    L₁ L₂ hL hs₁
  obtain ⟨s, -, -, huniq⟩ := existsUnique_reads4 fd₂ L₂ H₂
  exact (huniq s₁ hs₁').trans (huniq s₂ hs₂).symm

end Invariance

/-! ## 8.  Regrowths: anchor input, anchor uniqueness, and frame-class invariance -/

section Regrowth

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open GeometricLimitTransport (limitIso)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The anchor input of a regrowth** at a merged block of its limit, at valency four. -/
abbrev RegrowthAnchor4 (w : Regrowth core y degree)
    (block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks) :
    Prop :=
  AnchorInput4 w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) block

/-- **The wall metric of a facet regrowth**: every stable row other than the facet slot's is
nonzero, the facet slot's row vanishes, the contracted column is zero and every other column
is positive.  (Extracted from `ValencyThreeSplit.exists_regrowthAnchor`.) -/
theorem facet_rows (w : Regrowth core y degree) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y) :
    (∀ row, row ≠ w.frame.slot.symm e₀ → (GluingDatum.LengthMatrixPresentation.matrix
      w.frame.fullDim.labelling.presentation).mulVec (w.frame.coordsAt y) row ≠ 0) ∧
    (GluingDatum.LengthMatrixPresentation.matrix
      w.frame.fullDim.labelling.presentation).mulVec (w.frame.coordsAt y)
        (w.frame.slot.symm e₀) = 0 ∧
    w.frame.coordsAt y (w.frame.fullDim.labelling.targetEdge.symm (w.frame.edgeOf w.column)) = 0 ∧
    ∀ column, column ≠ w.frame.fullDim.labelling.targetEdge.symm (w.frame.edgeOf w.column) →
      0 < w.frame.coordsAt y column := by
  classical
  set k := w.frame with hk
  have hmul : ∀ row, (GluingDatum.LengthMatrixPresentation.matrix
      k.fullDim.labelling.presentation).mulVec (k.coordsAt y) row = y (k.slot row) :=
    fun row ↦ congrFun (k.mulVec_coordsAt y) row
  have hcol : k.fullDim.labelling.targetEdge.symm (k.edgeOf w.column) = w.column := by
    simp [Frame.edgeOf]
  refine ⟨fun row hrow ↦ ?_, ?_, InheritedLimitRows.zero_coordinate w, fun column hne ↦ ?_⟩
  · rw [hmul]
    refine ne_of_gt (hpt.2 _ ?_)
    intro h
    apply hrow
    rw [← h, Equiv.symm_apply_apply]
  · rw [hmul, Equiv.apply_symm_apply]
    exact hpt.1
  · rw [hcol] at hne
    exact w.degenerate.2 column hne

/-- **Stage 1 at valency four, at every facet regrowth**: a regrowth at a facet point of a
non-loop core slot whose limit's merged target vertex is four-valent has a merged block
carrying the full anchor input (the contraction forest from the single vanishing row's simple
end, and `nd(A) = 4` from `NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four`). -/
theorem exists_regrowthAnchor4 (w : Regrowth core y degree) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop : core.tail e₀ ≠ core.head e₀)
    (hval : (GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
      ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
        fst_ne_snd (w.frame.edgeOf w.column)⟩).card = 4) :
    ∃ block, RegrowthAnchor4 w block := by
  classical
  set k := w.frame with hk
  obtain ⟨hRows, hFacetZero, hZero, hPos⟩ := facet_rows w e₀ hpt
  have hNonneg : ∀ column, 0 ≤ k.coordsAt y column := by
    intro column
    by_cases h : column = k.fullDim.labelling.targetEdge.symm (k.edgeOf w.column)
    · rw [h, hZero]
    · exact le_of_lt (hPos column h)
  have hEnd : SingleRowForest.HasSimpleEnd k.data (k.fullDim.labelling.row.symm (k.slot.symm e₀)) := by
    have : k.fullDim.labelling.row.symm (k.slot.symm e₀) = k.ident.row.symm e₀ := by
      simp [Frame.slot]
    rw [this]
    exact hasSimpleEnd_of_ident k e₀ hloop
  have hForest : ContractionForest k.data _ _ (k.edgeOf w.column) :=
    SingleRowForest.contractionForest_of_single_row k.fullDim.labelling (k.coordsAt y) hNonneg
      (k.slot.symm e₀) hRows hEnd rfl hZero
  let star : W4TargetPairings.FourStar
      (contract k.target (fst_ne_snd (k.edgeOf w.column)) (k.numEdges_edgeOf w.column))
      ⟨_, fst_ne_snd (k.edgeOf w.column)⟩ := W4TargetPairings.FourStar.of_card hval
  obtain ⟨anchor, hFour⟩ := NonTrivalentUniqueFourValent.exists_wallBlock_nonDanglingValency_eq_four
    k.data k.fullDim rfl (fst_ne_snd (k.edgeOf w.column)) (k.numEdges_edgeOf w.column) star
    (WallAdmissibility.danglingCompatible_of_contractionForest k.data rfl _ _ hForest)
    (k.coordsAt y) (k.slot.symm e₀) hZero hPos hFacetZero
  refine ⟨NonTrivalentAnchorValency.mergedBlockOfWallBlock k.data rfl _ _ anchor, hForest, hval, ?_⟩
  rw [limA, NonTrivalentAnchorValency.mergedVertex_mergedBlockOfWallBlock]
  exact hFour

/-- **The anchor is the limit's only vertex of surviving valency four** at a facet regrowth
(`NonTrivalentUniqueFourValent.eq_of_nonDanglingValency_four`: two such vertices
would give two vanishing stable rows). -/
theorem eq_anchorOf_of_nd4 (w : Regrowth core y degree) {block} (H : RegrowthAnchor4 w block)
    (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y) (X : w.limit.SourceVertex)
    (hX : nonDanglingValency w.limit X = 4) : X = anchorOf w block := by
  obtain ⟨hRows, -, hZero, -⟩ := facet_rows w e₀ hpt
  exact NonTrivalentUniqueFourValent.eq_of_nonDanglingValency_four w.frame.data w.frame.fullDim
    rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) H.star
    H.compat (w.frame.coordsAt y) (w.frame.slot.symm e₀) hRows hZero X _ hX H.nd4

variable {c₂ : Core n p}

/-- **An isomorphism of regrowth limits carries anchor to anchor** at valency four. -/
theorem sourceVertexEquiv_anchorOf4 (w₁ : Regrowth core y degree) (w₂ : Regrowth c₂ y degree)
    {block₁} {block₂} (H₁ : RegrowthAnchor4 w₁ block₁) (H₂ : RegrowthAnchor4 w₂ block₂)
    (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (ψ : GeometricDatumIso w₁.limit w₂.limit) :
    ψ.sourceVertexEquiv (anchorOf w₁ block₁) = anchorOf w₂ block₂ := by
  apply eq_anchorOf_of_nd4 w₂ H₂ e₀ hpt
  exact (ψ.nonDanglingValency_map (connected_limit w₁) _).trans H₁.nd4

/-- **The read split is a frame-class invariant** (partner and `K`), for labellings transported
along the frame isomorphism's limit isomorphism. -/
theorem split4_eq_of_frameIso {w w' : Regrowth core y degree} (fi : FrameIso w.frame w'.frame)
    {block block'} (H : RegrowthAnchor4 w block) (H' : RegrowthAnchor4 w' block')
    (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (L : Labelling4 w.limit (anchorOf w block)) (L' : Labelling4 w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = (limitIso fi).sourceEdgeEquiv (L.e i))
    {s s' : Split4} (hs : Reads4 L s) (hs' : Reads4 L' s') : s = s' :=
  split4_eq_of_map w.frame.fullDim w'.frame.fullDim fi.datum (w.frame.edgeOf w.column)
    (w'.frame.edgeOf w'.column)
    (by rw [GeometricLimitTransport.targetEdge_edgeOf, GeometricLimitTransport.column_eq_of_frameIso fi])
    _ _ H H' (sourceVertexEquiv_anchorOf4 w w' H H' e₀ hpt (limitIso fi)) L L' hL hs hs'

/-- **`K` is a frame-class invariant, with no labelling at all**: any two regrowths presenting
one frame class read the same `K`, for arbitrary labellings of their limits. -/
theorem K_eq_of_frameIso {w w' : Regrowth core y degree} (fi : FrameIso w.frame w'.frame)
    {block block'} (H : RegrowthAnchor4 w block) (H' : RegrowthAnchor4 w' block')
    (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (L : Labelling4 w.limit (anchorOf w block)) (L' : Labelling4 w'.limit (anchorOf w' block'))
    {s s' : Split4} (hs : Reads4 L s) (hs' : Reads4 L' s') : s.K = s'.K := by
  have hψ := sourceVertexEquiv_anchorOf4 w w' H H' e₀ hpt (limitIso fi)
  obtain ⟨L'', hL''⟩ : ∃ L'' : Labelling4 w'.limit (anchorOf w' block'),
      ∀ i, L''.e i = (limitIso fi).sourceEdgeEquiv (L.e i) := by
    rw [← hψ]
    exact ⟨L.transport (limitIso fi) (connected_limit w), fun _ ↦ rfl⟩
  obtain ⟨s'', hs'', -, -⟩ := existsUnique_reads4 w'.frame.fullDim L'' H'
  rw [split4_eq_of_frameIso fi H H' e₀ hpt L L'' hL'' hs hs'']
  exact K_eq_of_reads4 w'.frame.fullDim L'' H' L' hs'' hs'

end Regrowth

/-! ## 9.  Valency-four metric facet limits: `K` as an index on the classes -/

section MetricLimit

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight SameMetricLimit)

variable {n p degree : ℕ} {c c' : Core n p} {y : Fin p → ℚ}

/-- **The admissible values of `K`** for given anchor indices (Part II, Case `{v4-nd4}`):
`0 ≤ K ≤ min(k_min - 1, |A| - k_max)`, label by label.  It is invariant under relabelling (it
quantifies over all labels) and is the `K`-half of `Indices4.Valid`. -/
def Indices4.KAdmissible (a : Indices4) (K : ℕ) : Prop := ∀ i, K + 1 ≤ a.k i ∧ K + a.k i ≤ a.A

theorem Indices4.kAdmissible_of_valid {a : Indices4} {s : Split4} (h : a.Valid s) :
    a.KAdmissible s.K := h.2

/-- **Two regrowths (over any cores) with valency-four anchors and an isomorphism of their
limits**: a labelling of the first limit transports to the second, the anchor indices agree,
both read splits are admissible for them, and equal read splits have equal local numbers
(`K`-rigidity across the isomorphism). -/
theorem regrowth_reads4 {c₁ c₂ : Core n p} (w₁ : Regrowth c₁ y degree)
    (w₂ : Regrowth c₂ y degree) {block₁} {block₂} (H₁ : RegrowthAnchor4 w₁ block₁)
    (H₂ : RegrowthAnchor4 w₂ block₂) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (ψ : GeometricDatumIso w₁.limit w₂.limit) (L₁ : Labelling4 w₁.limit (anchorOf w₁ block₁)) :
    ∃ (L₂ : Labelling4 w₂.limit (anchorOf w₂ block₂)) (s₁ s₂ : Split4),
      (∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i)) ∧ L₂.indices = L₁.indices ∧
      Reads4 L₁ s₁ ∧ Reads4 L₂ s₂ ∧ L₁.indices.Valid s₁ ∧ L₁.indices.Valid s₂ ∧
      (∀ P₁ : Bridge w₁.frame.data rfl (fst_ne_snd (w₁.frame.edgeOf w₁.column))
          (w₁.frame.numEdges_edgeOf w₁.column) block₁,
        ∀ P₂ : Bridge w₂.frame.data rfl (fst_ne_snd (w₂.frame.edgeOf w₂.column))
          (w₂.frame.numEdges_edgeOf w₂.column) block₂,
        s₁ = s₂ → w₁.frame.data.sourceEdgeIndex P₁.e₁ = w₂.frame.data.sourceEdgeIndex P₂.e₁) := by
  have hψ := sourceVertexEquiv_anchorOf4 w₁ w₂ H₁ H₂ e₀ hpt ψ
  obtain ⟨L₂, hL⟩ : ∃ L₂ : Labelling4 w₂.limit (anchorOf w₂ block₂),
      ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i) := by
    rw [← hψ]
    exact ⟨L₁.transport ψ (connected_limit w₁), fun _ ↦ rfl⟩
  have hidx := L₁.indices_eq_of_iso L₂ ψ hψ hL
  obtain ⟨s₁, hs₁, hv₁, -⟩ := existsUnique_reads4 w₁.frame.fullDim L₁ H₁
  obtain ⟨s₂, hs₂, hv₂, -⟩ := existsUnique_reads4 w₂.frame.fullDim L₂ H₂
  refine ⟨L₂, s₁, s₂, hL, hidx, hs₁, hs₂, hv₁, hidx ▸ hv₂, fun P₁ P₂ h ↦ ?_⟩
  subst h
  exact (numbers_eq_of_limitIso w₁.frame.fullDim w₂.frame.fullDim H₁ H₂ P₁ P₂ ψ hψ L₁ L₂ hL
    hs₁ hs₂).1

/-- **`K` is well defined on a frame class at a valency-four facet point**: some `K` is read by
every presenting regrowth, under every labelling. -/
theorem exists_classK {core : Core n p} (x : FrameClass core degree) (w₀ : Regrowth core y degree)
    (hw₀ : FrameClass.mk w₀.frame = x) {block₀} (H₀ : RegrowthAnchor4 w₀ block₀) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y) :
    ∃ K : ℕ, ∀ (w : Regrowth core y degree) (block) (_ : RegrowthAnchor4 w block)
      (L : Labelling4 w.limit (anchorOf w block)) (s : Split4),
      FrameClass.mk w.frame = x → Reads4 L s → s.K = K := by
  obtain ⟨L₀⟩ := nonempty_labelling4 _ _ H₀.nd4
  obtain ⟨s₀, hs₀, -, -⟩ := existsUnique_reads4 w₀.frame.fullDim L₀ H₀
  refine ⟨s₀.K, fun w block H L s hw hs ↦ ?_⟩
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (hw.trans hw₀.symm)
  exact K_eq_of_frameIso fi H H₀ e₀ hpt L L₀ hs hs₀

/-- **A valency-four metric facet limit**: every regrowth presenting it, on either side,
carries the anchor input.  Interface: discharged at every facet regrowth whose limit's merged
target vertex is four-valent (`v4Limit_of_facetPoint`). -/
def V4Limit (m : MetricFacetLimit c c' y degree) : Prop :=
  (∀ w : Regrowth c y degree, MetricFacetLimit.ofLeft (c' := c') w = m →
    ∃ block, RegrowthAnchor4 w block) ∧
  (∀ w : Regrowth c' y degree, MetricFacetLimit.ofRight (c := c) w = m →
    ∃ block, RegrowthAnchor4 w block)

/-- `V4Limit` at a facet point of a slot that is a non-loop in both cores reduces to the
four-valence of the merged target vertex of each presenting regrowth. -/
theorem v4Limit_of_facetPoint (m : MetricFacetLimit c c' y degree) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop : c.tail e₀ ≠ c.head e₀)
    (hloop' : c'.tail e₀ ≠ c'.head e₀)
    (hval : ∀ w : Regrowth c y degree, MetricFacetLimit.ofLeft (c' := c') w = m →
      (GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
        ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
          fst_ne_snd (w.frame.edgeOf w.column)⟩).card = 4)
    (hval' : ∀ w : Regrowth c' y degree, MetricFacetLimit.ofRight (c := c) w = m →
      (GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
        ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
          fst_ne_snd (w.frame.edgeOf w.column)⟩).card = 4) :
    V4Limit m :=
  ⟨fun w hw ↦ exists_regrowthAnchor4 w e₀ hpt hloop (hval w hw),
    fun w hw ↦ exists_regrowthAnchor4 w e₀ hpt hloop' (hval' w hw)⟩

variable {m : MetricFacetLimit c c' y degree}

theorem exists_classK_left (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (x : {x : FrameClass c degree // MSpecializesLeft x m}) :
    ∃ K : ℕ, ∀ (w : Regrowth c y degree) (block) (_ : RegrowthAnchor4 w block)
      (L : Labelling4 w.limit (anchorOf w block)) (s : Split4),
      FrameClass.mk w.frame = x.1 → Reads4 L s → s.K = K := by
  obtain ⟨w₀, hw₀, hm₀⟩ := x.2
  obtain ⟨block₀, H₀⟩ := hm.1 w₀ hm₀
  exact exists_classK x.1 w₀ hw₀ H₀ e₀ hpt

theorem exists_classK_right (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (x : {x : FrameClass c' degree // MSpecializesRight x m}) :
    ∃ K : ℕ, ∀ (w : Regrowth c' y degree) (block) (_ : RegrowthAnchor4 w block)
      (L : Labelling4 w.limit (anchorOf w block)) (s : Split4),
      FrameClass.mk w.frame = x.1 → Reads4 L s → s.K = K := by
  obtain ⟨w₀, hw₀, hm₀⟩ := x.2
  obtain ⟨block₀, H₀⟩ := hm.2 w₀ hm₀
  exact exists_classK x.1 w₀ hw₀ H₀ e₀ hpt

/-- **The index `K` on the near-side classes at a valency-four metric limit** (the `τL m` of
the census consumer). -/
noncomputable def kIndexL (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y) :
    {x : FrameClass c degree // MSpecializesLeft x m} → ℕ :=
  fun x ↦ Classical.choose (exists_classK_left hm e₀ hpt x)

/-- **The index `K` on the far-side classes at a valency-four metric limit** (`τR m`). -/
noncomputable def kIndexR (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y) :
    {x : FrameClass c' degree // MSpecializesRight x m} → ℕ :=
  fun x ↦ Classical.choose (exists_classK_right hm e₀ hpt x)

/-- `kIndexL` is the `K` every presenting regrowth reads, under every labelling. -/
theorem kIndexL_spec (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (x : {x : FrameClass c degree // MSpecializesLeft x m}) (w : Regrowth c y degree) {block}
    (H : RegrowthAnchor4 w block) (L : Labelling4 w.limit (anchorOf w block)) {s : Split4}
    (hw : FrameClass.mk w.frame = x.1) (hs : Reads4 L s) : kIndexL hm e₀ hpt x = s.K :=
  (Classical.choose_spec (exists_classK_left hm e₀ hpt x) w block H L s hw hs).symm

/-- `kIndexR` is the `K` every presenting regrowth reads, under every labelling. -/
theorem kIndexR_spec (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (x : {x : FrameClass c' degree // MSpecializesRight x m}) (w : Regrowth c' y degree) {block}
    (H : RegrowthAnchor4 w block) (L : Labelling4 w.limit (anchorOf w block)) {s : Split4}
    (hw : FrameClass.mk w.frame = x.1) (hs : Reads4 L s) : kIndexR hm e₀ hpt x = s.K :=
  (Classical.choose_spec (exists_classK_right hm e₀ hpt x) w block H L s hw hs).symm

/-- **Both indices take values in one admissible range.**  Fix any near-side regrowth `w₀`
presenting `m` and any labelling `L₀` of its limit's anchor: every class at `m`, on either
side, has `K` admissible for `L₀`'s anchor indices, `0 ≤ K ≤ min(k_min - 1, |A| - k_max)`.
This is the inclusion `range ⊆ admissible` of the census's "equal ranges"; the reverse
inclusion on each side is the existence of a class of every admissible `K`
(`ValencyFourRealisation.hex_of_resolved`). -/
theorem kIndex_admissible (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (w₀ : Regrowth c y degree) (hw₀ : MetricFacetLimit.ofLeft (c' := c') w₀ = m) {block₀}
    (H₀ : RegrowthAnchor4 w₀ block₀) (L₀ : Labelling4 w₀.limit (anchorOf w₀ block₀)) :
    (∀ x, L₀.indices.KAdmissible (kIndexL hm e₀ hpt x)) ∧
      (∀ x, L₀.indices.KAdmissible (kIndexR hm e₀ hpt x)) := by
  constructor
  · rintro ⟨x, w, hw, hwm⟩
    obtain ⟨block, H⟩ := hm.1 w hwm
    have hsame : SameMetricLimit (c := c) (c' := c') (Sum.inl w₀) (Sum.inl w) :=
      Quotient.exact (hw₀.trans hwm.symm)
    obtain ⟨ψ, -⟩ := hsame
    obtain ⟨L, s₀, s, -, hidx, -, hs, -, hv, -⟩ := regrowth_reads4 w₀ w H₀ H e₀ hpt ψ L₀
    rw [kIndexL_spec hm e₀ hpt ⟨x, w, hw, hwm⟩ w H L hw hs]
    exact Indices4.kAdmissible_of_valid hv
  · rintro ⟨x, w, hw, hwm⟩
    obtain ⟨block, H⟩ := hm.2 w hwm
    have hsame : SameMetricLimit (c := c) (c' := c') (Sum.inl w₀) (Sum.inr w) :=
      Quotient.exact (hw₀.trans hwm.symm)
    obtain ⟨ψ, -⟩ := hsame
    obtain ⟨L, s₀, s, -, hidx, -, hs, -, hv, -⟩ := regrowth_reads4 w₀ w H₀ H e₀ hpt ψ L₀
    rw [kIndexR_spec hm e₀ hpt ⟨x, w, hw, hwm⟩ w H L hw hs]
    exact Indices4.kAdmissible_of_valid hv

/-- `kIndex_admissible` with the reference regrowth on the far side. -/
theorem kIndex_admissible_right (hm : V4Limit m) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y) (w₀ : Regrowth c' y degree)
    (hw₀ : MetricFacetLimit.ofRight (c := c) w₀ = m) {block₀}
    (H₀ : RegrowthAnchor4 w₀ block₀) (L₀ : Labelling4 w₀.limit (anchorOf w₀ block₀)) :
    (∀ x, L₀.indices.KAdmissible (kIndexL hm e₀ hpt x)) ∧
      (∀ x, L₀.indices.KAdmissible (kIndexR hm e₀ hpt x)) := by
  constructor
  · rintro ⟨x, w, hw, hwm⟩
    obtain ⟨block, H⟩ := hm.1 w hwm
    have hsame : SameMetricLimit (c := c) (c' := c') (Sum.inr w₀) (Sum.inl w) :=
      Quotient.exact (hw₀.trans hwm.symm)
    obtain ⟨ψ, -⟩ := hsame
    obtain ⟨L, s₀, s, -, hidx, -, hs, -, hv, -⟩ := regrowth_reads4 w₀ w H₀ H e₀ hpt ψ L₀
    rw [kIndexL_spec hm e₀ hpt ⟨x, w, hw, hwm⟩ w H L hw hs]
    exact Indices4.kAdmissible_of_valid hv
  · rintro ⟨x, w, hw, hwm⟩
    obtain ⟨block, H⟩ := hm.2 w hwm
    have hsame : SameMetricLimit (c := c) (c' := c') (Sum.inr w₀) (Sum.inr w) :=
      Quotient.exact (hw₀.trans hwm.symm)
    obtain ⟨ψ, -⟩ := hsame
    obtain ⟨L, s₀, s, -, hidx, -, hs, -, hv, -⟩ := regrowth_reads4 w₀ w H₀ H e₀ hpt ψ L₀
    rw [kIndexR_spec hm e₀ hpt ⟨x, w, hw, hwm⟩ w H L hw hs]
    exact Indices4.kAdmissible_of_valid hv

/-- **The anchor indices of a valency-four metric limit**: some presenting regrowth (on either
side) and a labelling of its anchor, whose indices bound every class's `K` on both sides. -/
theorem exists_reference (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y) :
    ∃ a : Indices4, (∀ x, a.KAdmissible (kIndexL hm e₀ hpt x)) ∧
      ∀ x, a.KAdmissible (kIndexR hm e₀ hpt x) := by
  obtain ⟨r, hr⟩ := Quotient.exists_rep m
  rcases r with w₀ | w₀
  · obtain ⟨block₀, H₀⟩ := hm.1 w₀ hr
    obtain ⟨L₀⟩ := nonempty_labelling4 _ _ H₀.nd4
    exact ⟨L₀.indices, kIndex_admissible hm e₀ hpt w₀ hr H₀ L₀⟩
  · obtain ⟨block₀, H₀⟩ := hm.2 w₀ hr
    obtain ⟨L₀⟩ := nonempty_labelling4 _ _ H₀.nd4
    exact ⟨L₀.indices, kIndex_admissible_right hm e₀ hpt w₀ hr H₀ L₀⟩

/-- **Equal ranges from per-`K` existence.**  If every admissible `K` of the reference indices
is realised by a class on each side, the two `K`-ranges are equal (both are the admissible
range, by `kIndex_admissible`).  The existence is the valency-four `K`-preserving transfer,
`ValencyFourRealisation.hex_of_resolved`. -/
theorem range_kIndex_eq (hm : V4Limit m) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (a : Indices4) (haL : ∀ x, a.KAdmissible (kIndexL hm e₀ hpt x))
    (haR : ∀ x, a.KAdmissible (kIndexR hm e₀ hpt x))
    (hexL : ∀ K, a.KAdmissible K → ∃ x, kIndexL hm e₀ hpt x = K)
    (hexR : ∀ K, a.KAdmissible K → ∃ x, kIndexR hm e₀ hpt x = K) :
    Set.range (kIndexL hm e₀ hpt) = Set.range (kIndexR hm e₀ hpt) := by
  ext K
  constructor
  · rintro ⟨x, rfl⟩
    exact hexR _ (haL x)
  · rintro ⟨x, rfl⟩
    exact hexL _ (haR x)

/-- **The valency-four clause of `FacetCensus.MetricCensus`.**  At a valency-four metric facet
limit `m`, the index `K` (`kIndexL`, `kIndexR`) gives the census at `m` as soon as it is
injective on each side (`K`-rigidity in the exhaustion sense: two classes of one core at `m`
with the same `K` are equal) and each side realises the other's values.  The index is `K`
alone: it needs no labelling (`K_eq_of_frameIso`), whereas the pairing is only defined
relative to a labelling of `m` and moves under label-moving automorphisms of `m`. -/
theorem metricCensus_clause_of_kIndex (hm : V4Limit m) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y)
    (hinjL : Function.Injective (kIndexL hm e₀ hpt))
    (hinjR : Function.Injective (kIndexR hm e₀ hpt))
    (hrange : Set.range (kIndexL hm e₀ hpt) = Set.range (kIndexR hm e₀ hpt)) :
    ∃ (ι : Type) (τL : {x : FrameClass c degree // MSpecializesLeft x m} → ι)
      (τR : {x : FrameClass c' degree // MSpecializesRight x m} → ι),
      Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR :=
  ⟨ℕ, kIndexL hm e₀ hpt, kIndexR hm e₀ hpt, hinjL, hinjR, hrange⟩

/-- **The valency-four clause from injectivity and per-`K` existence on both sides.**  The
existence hypotheses are relative to the anchor indices of an actual presenting regrowth (on
either side) and a labelling of its anchor -- the indices of `m` -- so they are exactly the
`K`-preserving existence transfers (`ValencyFourRealisation.hex_of_resolved`): every
admissible `K` of `m` is realised by a class of each core. -/
theorem metricCensus_clause_of_realised (hm : V4Limit m) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y)
    (hinjL : Function.Injective (kIndexL hm e₀ hpt))
    (hinjR : Function.Injective (kIndexR hm e₀ hpt))
    (hexL : ∀ (w₀ : Regrowth c y degree), MetricFacetLimit.ofLeft (c' := c') w₀ = m →
      ∀ {block₀} (_ : RegrowthAnchor4 w₀ block₀) (L₀ : Labelling4 w₀.limit (anchorOf w₀ block₀))
        (K : ℕ), L₀.indices.KAdmissible K →
        (∃ x, kIndexL hm e₀ hpt x = K) ∧ ∃ x, kIndexR hm e₀ hpt x = K)
    (hexR : ∀ (w₀ : Regrowth c' y degree), MetricFacetLimit.ofRight (c := c) w₀ = m →
      ∀ {block₀} (_ : RegrowthAnchor4 w₀ block₀) (L₀ : Labelling4 w₀.limit (anchorOf w₀ block₀))
        (K : ℕ), L₀.indices.KAdmissible K →
        (∃ x, kIndexL hm e₀ hpt x = K) ∧ ∃ x, kIndexR hm e₀ hpt x = K) :
    ∃ (ι : Type) (τL : {x : FrameClass c degree // MSpecializesLeft x m} → ι)
      (τR : {x : FrameClass c' degree // MSpecializesRight x m} → ι),
      Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR := by
  refine metricCensus_clause_of_kIndex hm e₀ hpt hinjL hinjR ?_
  obtain ⟨r, hr⟩ := Quotient.exists_rep m
  rcases r with w₀ | w₀
  · obtain ⟨block₀, H₀⟩ := hm.1 w₀ hr
    obtain ⟨L₀⟩ := nonempty_labelling4 _ _ H₀.nd4
    obtain ⟨haL, haR⟩ := kIndex_admissible hm e₀ hpt w₀ hr H₀ L₀
    exact range_kIndex_eq hm e₀ hpt L₀.indices haL haR
      (fun K hK ↦ (hexL w₀ hr H₀ L₀ K hK).1) (fun K hK ↦ (hexL w₀ hr H₀ L₀ K hK).2)
  · obtain ⟨block₀, H₀⟩ := hm.2 w₀ hr
    obtain ⟨L₀⟩ := nonempty_labelling4 _ _ H₀.nd4
    obtain ⟨haL, haR⟩ := kIndex_admissible_right hm e₀ hpt w₀ hr H₀ L₀
    exact range_kIndex_eq hm e₀ hpt L₀.indices haL haR
      (fun K hK ↦ (hexR w₀ hr H₀ L₀ K hK).1) (fun K hK ↦ (hexR w₀ hr H₀ L₀ K hK).2)

/-- The clause above is literally `FacetCensus.MetricCensus` at one limit: a census whose
every limit is valency four is a `MetricCensus`.  (The census assembly dispatches per limit.) -/
example (h : ∀ m : MetricFacetLimit c c' y degree,
    ∃ (ι : Type) (τL : {x : FrameClass c degree // MSpecializesLeft x m} → ι)
      (τR : {x : FrameClass c' degree // MSpecializesRight x m} → ι),
      Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR) :
    FacetCensus.MetricCensus c c' degree y := h

end MetricLimit

/-! ## 10.  Genus-six data -/

section P1Data

/-- **The genus-six `K`-families, arithmetically**: at the profile `(3; 2, 2, 2, 2)` every
pairing has side sum `4`, the admissible `K` are `0, 1`, and the prescribed bridge index and
branch sizes are `(k₁, |X|, |Y|) = (3, 3, 3)` at `K = 0` and `(1, 2, 2)` at `K = 1` --
exactly the values `k₁ ∈ {3, 1}` and the branch sizes that a computer check reads off every
class of such a family. -/
theorem p1_profile_numbers : ∀ j : Fin 4, j ≠ 0 →
    ((⟨3, fun _ ↦ 2⟩ : Indices4).bridge ⟨j, 0⟩, (⟨3, fun _ ↦ 2⟩ : Indices4).sizeZero ⟨j, 0⟩,
        (⟨3, fun _ ↦ 2⟩ : Indices4).sizeOther ⟨j, 0⟩) = (3, 3, 3) ∧
      ((⟨3, fun _ ↦ 2⟩ : Indices4).bridge ⟨j, 1⟩, (⟨3, fun _ ↦ 2⟩ : Indices4).sizeZero ⟨j, 1⟩,
        (⟨3, fun _ ↦ 2⟩ : Indices4).sizeOther ⟨j, 1⟩) = (1, 2, 2) ∧
      (⟨3, fun _ ↦ 2⟩ : Indices4).Valid ⟨j, 0⟩ ∧ (⟨3, fun _ ↦ 2⟩ : Indices4).Valid ⟨j, 1⟩ ∧
      ¬ (⟨3, fun _ ↦ 2⟩ : Indices4).Valid ⟨j, 2⟩ := by
  unfold Indices4.bridge Indices4.sizeZero Indices4.sizeOther Indices4.side Indices4.total
    Indices4.Valid
  decide

/-- The other degree-four profile with a two-member family, `(4; 2, 2, 3, 3)`: admissible
`K ∈ {0, 1}` as well (`min(k₂ - 1, |A| - k₅) = min(1, 1)`). -/
example :
    let a : Indices4 := ⟨4, ![2, 2, 3, 3]⟩
    a.KAdmissible 0 ∧ a.KAdmissible 1 ∧ ¬ a.KAdmissible 2 := by
  intro a
  refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun h ↦ absurd (h 0).1 (by decide)⟩ <;>
    fin_cases i <;> decide

end P1Data

end DraismaVargas.Count.ValencyFourSplit
