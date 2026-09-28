import DraismaVargasCount.ValencyFourSplit
import DraismaVargasCount.ValencyThreeCoreSlots
import DraismaVargasCount.RowGeodesic
import DraismaVargasCount.Integrality
import DraismaVargasCount.CensusAssembly

set_option autoImplicit false

/-!
# Valency-four rigidity: `K` is injective on the classes at a valency-four metric limit

**Source.**  Vargas, Part II (arXiv:2609.09109), the valency-4 limits (`subsec-case-v4`, Case
`{v4-nd4}`): "the local part of `φ^{(q)}` contracting to `A` is uniquely determined by `|A_1|`,
`|A_2|`, `k_1` and the base tree", and "each value of `K` produces a distinct morphism for each
base tree"; Draisma--Vargas Part I (arXiv:1909.12924), `prop-local` and `lemma-pass-once` (rows
turn only over leaves).  This file proves `Function.Injective (kIndexL hm e₀ hpt)` and
`Function.Injective (kIndexR hm e₀ hpt)`, and shows that no valency-four loop merge is needed.
It builds on `ValencyFourSplit` (the index `K`),
`M11StarExhaustionProof.nonempty_transportFree_of_rel`,
`ValencyThreeResolutionMatch.pendant_at_wall_forest`, `ValencyThreeRigidity`,
`ValencyThreeCoreSlots` (`row_inRow_map`, `row_e₁`, the core reading) and the census target
`CensusAssembly.V4InputsSupply`.  The injectivity is the first two conjuncts of
`CensusAssembly.V4InputsSupply`, which `ValencyFourRealisation.v4InputsSupply` completes; that
feeds the valency-four clause of the type changes in step 3 of `DraismaVargasCount/Assembly.lean`
(`Assembly.typeChanges_genusSix`).

## The result, in one paragraph

Two classes of one connected core (`3 ≤ n`) at one valency-four metric facet limit with the
same `K` are equal (`kIndexL_injective_of_v4`, `kIndexR_injective_of_v4`), at **every** facet
point: no genericity, no resolved datum, no oddness, no pairing in the index.  The argument has
three stages, numbered 3--5 as in the valency-three argument of `ValencyThreeRigidity`: stage 3
reads the partner of label `0`; stage 4 extends a labelled metric isomorphism across the
anchor; stage 5 (`ValencyThreeRigidity.frameIso_of_columns`) pins the identification by the
columns.  Stage 3 is read on the core (`partner_eq_of_metricIso`), because at a valency-four
facet the core **never** has a slot parallel to the vanishing slot (`noParallel_of_anchor4`) --
so a valency-four analogue of the loop merge of `ValencyThreeLoopMerge` is vacuous.
Stages 4--5 (`frameClass_eq_of_reads4`): the incoming resolution of every class is "active
sheets plus singletons" on every merged class (`resShape`), its class counts are fixed by the
limit data and, at the anchor, by the bridge index `k₁` which `K` fixes (`ClassFacts.eq`,
`hK_of_reads4`); a colouring permutation `τ` and pendant realignments of the four wall
occurrences (`exists_realign_good`) give a decoupled transport (`exists_transport`), and
`ValencyThreeRigidity.extendsMetric_of_transportFree` with
`ValencyThreeRigidity.frameIso_of_columns` conclude.

## What is proved

* §1--§3 `exists_equiv_fiber`, `exists_perm_extend`; `pendantIsoW` (the pendant automorphism
  with the one-wall-class hypothesis replaced by class preservation), `pendant_of_active`,
  **`exists_realign`**; `ResShape`, **`transportFree_of_shape`** (a
  `ResolutionExpansionFree.TransportFree` from one wall permutation `τ`, as in
  `M11StarExhaustionProof.nonempty_transportFree_of_rel`).
* §4--§7 the incoming resolution on every merged class at a change-free wall (`Act`,
  `vertex_rel_iff`, `contracted_rel_iff`, `contracted_survives_iff`), boundary survivors as limit
  survivors (`bdAt_eq_image`), `ClassFacts` and **`ClassFacts.eq`** (sizes determined by the
  limit, and by `z` at a class with two limit survivors on each side), **`classFacts`**.
* §8--§9 `resolution_facts`, **`resShape`** (both placements), `label_side`,
  `label_target_injective`, `exists_label` (the four labels sit on the four wall occurrences).
* §10--§14 `card_four`, **`exists_tau`**, `exists_perm_extend2`, **`exists_rho`**,
  `act_of_survives`, `limit_active_of_act`, `eq_of_limit_inactive`, `classFactsUV`,
  `rSurv_map`, `rCnt_true_map`, `cnt_both_eq_index` (the sheets active at both ends of the
  anchor class are the bridge's), `repr_eq_block_of_two`, **`hK_of_reads4`**,
  `exists_realign_good`, **`exists_transport`**.
* §15 `rightW_true_iff`, `rightW_false_iff`, `right_label_iff` (a label's incoming side is read
  off the split), **`frameClass_eq_of_reads4`** (stages 4--5: equal splits along a labelled
  metric isomorphism give one class, for every class).
* §16--§17 `frameOfBridge`, `Paired4`, **`paired4_iff_coreShare`**, `paired4_zero_iff`,
  `wallRows4`, `slot_transport4`, **`partner_eq_of_metricIso`** (stage 3, universal form, at a
  core with no slot parallel to `e₀`), **`frameClass_eq_of_metricIso4`**, `kIndexL_injective`,
  `kIndexR_injective` (with `NoParallel`).
* §18--§19 walks in a tree as lists of occurrences: `walkEnd`, `isWalkFrom_append`,
  `isWalkFrom_reverse`, `not_closed_walk`, `IsTrailFrom`, **`exists_reduce`** (free
  reduction), **`no_split_walk`**, `exists_split_turnFree`.
* §20--§22 `SrcChain` (a stable row read from `W4StableSource.traverse`), `srcChain_trail`,
  `srcChain_walk`, **`isLeaf_of_turn`** (a row turns only over a leaf), **`turn_pairs`** (all
  turns of a row use one pair of occurrences), **`exists_split_row`** (the target walk of a row
  is two geodesics joined at one turn), **`walk_eq_of_walkEnd_eq`** (geodesic uniqueness),
  `no_split_loop`.
* §23 **`noParallel_of_anchor4`** and **`not_loopAtEnd_of_anchor4`**: at a valency-four facet
  regrowth the core has no slot parallel to `e₀` and no self-loop at an end of `e₀`, i.e. the
  limit's stable graph has no loop at the anchor.
* §24 **`kIndexL_injective_of_v4`**, **`kIndexR_injective_of_v4`** (at every `FacetPoint`),
  **`injective_of_resolved`** (the two injectivity conjuncts of
  `CensusAssembly.V4InputsSupply` at every `ResolvedDatum`), **`v4InputsSupply_of_realisation`**
  (`V4InputsSupply` from per-`K` realisation alone).

## Remarks

* **No valency-four loop merge.**  One might expect that when `H₀` has a loop at the anchor, the
  two types that give one labelled core must be identified, as at valency three
  (`ValencyThreeLoopMerge`).  The premise never holds.  At a valency-four facet the core has
  neither a slot parallel to `e₀` (`noParallel_of_anchor4`) nor a self-loop at an end of `e₀`
  (`not_loopAtEnd_of_anchor4`), so `H₀ = c/e₀` has no loop at the merged vertex.  The
  mechanism: the four anchor survivors lie over four distinct target occurrences (Part II, the
  opening of `subsec-case-v4`, from Case (r0-nd3) of Part I's `prop-local`), so a row closing up
  at the anchor would leave and re-enter the anchor fibre by two different target occurrences,
  while a row's target walk is two geodesics joined at one leaf turn.  (At valency three the
  parallel rows exist and use two survivors over one leaf edge plus an internal occurrence over
  `t₁`; those are what `ValencyThreeLoopMerge` identifies.)  A computer enumeration, not part
  of this library, agrees: over the genus-four catalogue it finds 2550 parallel rows at 6840
  valency-three facets and **none** at 2835 valency-four facets, and over a set of genus-six
  members 342 and **none** at 651.
* **The index is `K` alone**, not a pair (pairing, `K`): the pairing is fixed by the core and
  the labelled limit (`partner_eq_of_metricIso`).
* **The valency-three transport carries over, widened.**  The valency-three route to stage 4
  (classify the resolution per merged class, transport via
  `M11StarExhaustionProof.nonempty_transportFree_of_rel`, realign with
  `ValencyThreeResolutionMatch.pendant_at_wall_forest`) works here, but at valency four every
  merged class must be matched, not only the anchor's; the non-anchor classes are matched by the
  limit data alone and the anchor class by `k₁`, which `K` determines (`ClassFacts.eq`).  The
  pendant realignment is widened to several wall classes (`pendantIsoW`).
* **Stage 5 is valency-free**: `ValencyThreeRigidity.frameIso_of_columns` is used unchanged.
* **`WallRows` at valency four.**  `ValencyThreeCoreSlots` produces `WallRows` at valency three;
  this file produces it at valency four (`wallRows4`).

## Hypotheses

* **Per-`K` realisation on both sides** (the third and fourth conjuncts of
  `CensusAssembly.V4InputsSupply`, `hexL`/`hexR` of
  `ValencyFourSplit.metricCensus_clause_of_realised`) is not proved here;
  `v4InputsSupply_of_realisation` takes exactly them.  They are
  `ValencyFourRealisation.hex_of_resolved` (through the general-`K` link of `GeneralKLink`), so
  `V4InputsSupply` and `V4ClauseSupply (4*2+2) (6*2+3) (2+2)` hold with no hypothesis
  (`ValencyFourRealisation.v4InputsSupply`, `ValencyFourRealisation.v4ClauseSupply_genusSix`).
* `core.Connected` and `3 ≤ n` (those of `ValencyThreeRigidity.frameIso_of_columns`),
  `FacetPoint e₀ y` (the vanishing row), and `V4Limit m` (every presenting regrowth anchored;
  producer `ValencyFourSplit.v4Limit_of_facetPoint`), all as in `ValencyFourSplit` and
  `ValencyThreeRigidity`.
* `noParallel_of_anchor4` / `not_loopAtEnd_of_anchor4` are not exhibited on a concrete regrowth
  (no facet regrowth over a literal gluing datum is constructed here); their hypotheses are
  those of `ValencyFourSplit.exists_regrowthAnchor4`.
* Nothing here concerns valency two.

## New `Prop`s

`ResShape`, `Act`, `ClassFacts`, `Agrees`, `Paired4`, `IsTrailFrom`, `SrcChain`: each docstring
names its producer and consumer; each is produced by a theorem of this file (`resShape`,
`classFacts`, `paired4_zero_iff`, `srcChain_trail`, `traverse_srcChain`; `Agrees` holds for the
incoming side assignment itself) and consumed downstream here.
-/

namespace DraismaVargas.Count.ValencyFourRigidity

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification
open W4StableSource WallDegeneration FullDimensionalSource PrunedFibreValency PrunedFibreTree
  FullContractionFibre

/-! ## 1.  Permutations with prescribed colours -/

section Colouring

/-- **Equal fibres give a colour-preserving bijection.** -/
theorem exists_equiv_fiber {α β κ : Type*} [Finite α] [Finite β] (f : α → κ) (g : β → κ)
    (h : ∀ k, Nat.card {a // f a = k} = Nat.card {b // g b = k}) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a :=
  ⟨Equiv.ofFiberEquiv (fun k ↦ (Finite.card_eq.mp (h k)).some),
    fun a ↦ Equiv.ofFiberEquiv_map _ a⟩

/-- Counting a subtype by a second predicate. -/
theorem card_and_add_card_and_not {α : Type*} [Finite α] (R C : α → Prop) :
    Nat.card {x // C x ∧ R x} + Nat.card {x // C x ∧ ¬ R x} = Nat.card {x // C x} := by
  classical
  have e1 : {x // C x ∧ R x} ≃ {y : {x // C x} // R y.1} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter C R).symm
  have e2 : {x // C x ∧ ¬ R x} ≃ {y : {x // C x} // ¬ R y.1} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter C (fun x ↦ ¬ R x)).symm
  rw [Nat.card_congr e1, Nat.card_congr e2, ← Nat.card_sum,
    Nat.card_congr (Equiv.sumCompl fun y : {x // C x} ↦ R y.1)]

variable {d : ℕ} {κ : Type*}

/-- **Extending a colour-preserving partial bijection to a colour-preserving permutation.** -/
theorem exists_perm_extend (cls : Fin d → κ) (P Q : Fin d → Prop)
    (g : {x // P x} ≃ {y // Q y}) (hg : ∀ x, cls (g x).1 = cls x.1) :
    ∃ π : Equiv.Perm (Fin d), (∀ x (hx : P x), π x = (g ⟨x, hx⟩).1) ∧ ∀ x, cls (π x) = cls x := by
  classical
  have hPQ : ∀ k, Nat.card {x // cls x = k ∧ P x} = Nat.card {y // cls y = k ∧ Q y} := by
    intro k
    have e0 : {a : {x // P x} // cls a.1 = k} ≃ {b : {y // Q y} // cls b.1 = k} :=
      g.subtypeEquiv (p := fun a ↦ cls a.1 = k) (q := fun b ↦ cls b.1 = k)
        (fun a ↦ by rw [hg a])
    have e1 : {a : {x // P x} // cls a.1 = k} ≃ {x // cls x = k ∧ P x} :=
      (Equiv.subtypeSubtypeEquivSubtypeInter P (fun x ↦ cls x = k)).trans
        (Equiv.subtypeEquivRight fun _ ↦ and_comm)
    have e2 : {b : {y // Q y} // cls b.1 = k} ≃ {y // cls y = k ∧ Q y} :=
      (Equiv.subtypeSubtypeEquivSubtypeInter Q (fun y ↦ cls y = k)).trans
        (Equiv.subtypeEquivRight fun _ ↦ and_comm)
    exact Nat.card_congr (e1.symm.trans (e0.trans e2))
  have hc : ∀ k, Nat.card {a : {x // ¬ P x} // cls a.1 = k} =
      Nat.card {b : {y // ¬ Q y} // cls b.1 = k} := by
    intro k
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun x ↦ ¬ P x)
      (fun x ↦ cls x = k)),
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun y ↦ ¬ Q y)
      (fun y ↦ cls y = k))]
    have h1 := card_and_add_card_and_not P (fun x ↦ cls x = k)
    have h2 := card_and_add_card_and_not Q (fun y ↦ cls y = k)
    rw [hPQ k] at h1
    have e1 : {x // ¬ P x ∧ cls x = k} ≃ {x // cls x = k ∧ ¬ P x} :=
      Equiv.subtypeEquivRight fun _ ↦ and_comm
    have e2 : {x // ¬ Q x ∧ cls x = k} ≃ {x // cls x = k ∧ ¬ Q x} :=
      Equiv.subtypeEquivRight fun _ ↦ and_comm
    rw [Nat.card_congr e1, Nat.card_congr e2]
    omega
  obtain ⟨e, he⟩ := exists_equiv_fiber (fun a : {x // ¬ P x} ↦ cls a.1)
    (fun b : {y // ¬ Q y} ↦ cls b.1) hc
  refine ⟨Equiv.subtypeCongr g e, fun x hx ↦ ?_, fun x ↦ ?_⟩
  · simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
  · by_cases hx : P x
    · have : Equiv.subtypeCongr g e x = (g ⟨x, hx⟩).1 := by
        simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
      rw [this]; exact hg _
    · have : Equiv.subtypeCongr g e x = (e ⟨x, hx⟩).1 := by
        simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
      rw [this]; exact he _

end Colouring

/-! ## 2.  Pendant realignment across several wall classes -/

section PendantW

open TargetBranchRegion
open W3Nd2StarExhaustionProof (Pendant branchPerm relabel_eq_self_of_singleton relabel_refl')

variable {T : CFGraph} {degree : ℕ} {M : GluingDatum T degree} {wall root : T.V}
  {hRoot : root ≠ wall} {D : Fin degree → Prop}

/-- **The pendant automorphism, for a sheet set spread over several wall classes**: the
pendant automorphism `W3Nd2StarExhaustionProof.pendantIso` with its one-class hypothesis
replaced by the
permutation's own class preservation at the wall. -/
def pendantIsoW (hP : Pendant M wall root hRoot D) (π : Equiv.Perm (Fin degree))
    (hπ : ∀ x, ¬ D x → π x = x) (hW : ∀ s, D s → (M.vertexPartition wall).Rel (π s) s) :
    GeometricDatumIso M M where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends _ := Or.inl rfl
  vertexPerm v := branchPerm (vertexMoved wall root hRoot v) π
  edgePerm e := branchPerm (edgeMoved wall root hRoot e) π
  vertexPartition v := by
    change M.vertexPartition v = (M.vertexPartition v).relabel _
    unfold branchPerm
    split_ifs with h
    · exact (relabel_eq_self_of_singleton _ D π hπ (hP.vertex_single v h)).symm
    · exact (relabel_refl' _).symm
  edgePartition e := by
    change M.edgePartition e = (M.edgePartition e).relabel _
    unfold branchPerm
    split_ifs with h
    · exact (relabel_eq_self_of_singleton _ D π hπ (hP.edge_single e h)).symm
    · exact (relabel_refl' _).symm
  compatible e v hv s := by
    unfold branchPerm
    by_cases he : edgeMoved wall root hRoot e = true <;>
      by_cases hvm : vertexMoved wall root hRoot v = true
    · rw [if_pos he, if_pos hvm, Equiv.symm_apply_apply]; rfl
    · rw [if_pos he, if_neg hvm]
      have hWall : v = wall := by
        rcases hv with h | h
        · subst h
          exact boundary_left wall root hRoot e (by rw [he]; simpa using hvm)
        · subst h
          exact boundary_right wall root hRoot e (by rw [he]; simpa using hvm)
      subst hWall
      change (M.vertexPartition v).Rel (π s) s
      by_cases hs : D s
      · exact hW s hs
      · rw [hπ s hs]; rfl
    · exfalso
      apply he
      unfold edgeMoved
      rcases hv with h | h
      · rw [h, hvm]; simp
      · rw [h, hvm]; simp
    · rw [if_neg he, if_neg hvm]
      rfl

end PendantW

section Realign

open TargetBranchRegion DanglingSideStructure
open DraismaVargas.Count.WallStar (Regrowth)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W3Nd2StarExhaustionProof (Pendant branchPerm farEnd farEnd_ne edgeMoved_self edgeMoved_other
  exists_branch_cut mem_side_of_moved)
open ValencyThreeResolutionMatch (ends_of_mem)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The pendant hypothesis at a regrowth wall, for sheets in active wall classes**
(`ValencyThreeResolutionMatch.pendant_at_wall_forest`, with its one-class hypothesis replaced
by the activity of
each sheet's own wall class). -/
theorem pendant_of_active (w : Regrowth core y degree)
    (hForest : ContractionForest w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
      (w.frame.edgeOf w.column))
    (hNoGlue : DanglingEdgeNoGlue w.limit)
    {e : (w.frame.limitTarget w.column).edges}
    (hInc : (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
        mergeVertex w ∨
      (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
        mergeVertex w) (D : Fin degree → Prop)
    (hAct : ∀ s, D s → 0 < nonDanglingValency w.limit (w.limit.sourceEndpoint (mergeVertex w) s))
    (hDang : ∀ s, D s → IsDangling w.limit (w.limit.sourceEdge e s)) :
    Pendant w.limit (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) D := by
  have hVD : ∀ v, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) v = true →
      ∀ s, D s → nonDanglingValency w.limit (w.limit.sourceEndpoint v s) = 0 := by
    intro v hv s hs
    obtain ⟨cut⟩ := exists_branch_cut w.limit hInc
      (show (w.limit.vertexPartition (mergeVertex w)).Rel s s from rfl) (hAct s hs) (hDang s hs)
    exact nonDanglingValency_eq_zero_of_mem_side w.limit cut
      (mem_side_of_moved w.limit (farEnd_ne hInc) s cut rfl hv)
  have hED : ∀ f, edgeMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) f = true →
      ∀ s, D s → IsDangling w.limit (w.limit.sourceEdge f s) := by
    intro f hf s hs
    have hEnd : ∃ u, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) u =
        true ∧ f ∈ GluingDatum.incidentEdges u := by
      unfold edgeMoved at hf
      rcases Bool.or_eq_true_iff.mp hf with h | h
      · exact ⟨_, h, by simp [GluingDatum.incidentEdges]⟩
      · exact ⟨_, h, by simp [GluingDatum.incidentEdges]⟩
    obtain ⟨u, hu, hMem⟩ := hEnd
    exact (nonDanglingValency_eq_zero_iff w.limit _).mp (hVD u hu s hs) _
      (incident_sourceEdge_sourceEndpoint w.limit u f hMem s)
  refine ⟨?_, ?_, hVD, hED⟩
  · intro v hv s hs t hst
    have hvWall : v ≠ mergeVertex w := by
      intro h
      rw [h, vertexMoved_wall] at hv
      exact Bool.false_ne_true hv
    have hva : v.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1 := by
      intro h
      exact hvWall (Subtype.ext h)
    have hvb : v.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2 := v.2
    have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
      hForest
    set x := w.frame.data.sourceEndpoint v.1 s
    have hMap := WallDegeneration.nonDanglingValency_sourceVertexMap w.frame.data hCompat x hva hvb
    have hPart : w.limit.vertexPartition v = w.frame.data.vertexPartition v.1 :=
      contractVertexPartition_of_ne w.frame.data _ _ hva
    have hImage : sourceVertexMap w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) x = w.limit.sourceEndpoint v s := by
      change w.limit.sourceEndpoint (GraphContraction.fold _ _ v.1)
        ((w.frame.data.vertexPartition v.1).repr s) = _
      have hFold : GraphContraction.fold w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
          v.1 = v := GraphContraction.fold_coe _ _ v
      refine (congrArg (fun z : (w.frame.limitTarget w.column).V ↦
        w.limit.sourceEndpoint z ((w.frame.data.vertexPartition v.1).repr s)) hFold).trans ?_
      apply M11StarExhaustionProof.sourceEndpoint_of_rel
      rw [hPart]
      exact (w.frame.data.vertexPartition v.1).rel_repr_left s
    rw [hImage] at hMap
    have h0 : nonDanglingValency w.frame.data x = 0 := hMap.symm.trans (hVD v hv s hs)
    obtain ⟨hOne, -⟩ := PendantFibre.degree_one_of_nonDanglingValency_zero w.frame.fullDim x h0
    change (w.frame.data.vertexPartition v.1).blockCard
      ((w.frame.data.vertexPartition v.1).repr s) = 1 at hOne
    have hBlock := (w.frame.data.vertexPartition v.1).block_eq_of_rel
      ((w.frame.data.vertexPartition v.1).rel_repr_right s)
    unfold SheetPartition.blockCard at hOne
    rw [← hBlock] at hOne
    have hSingle := (w.frame.data.vertexPartition v.1).block_eq_singleton_of_blockCard_eq_one
      s hOne
    rw [hPart] at hst
    have hMem := ((w.frame.data.vertexPartition v.1).mem_block_iff s t).mpr hst
    rw [hSingle, Finset.mem_singleton] at hMem
    exact hMem
  · intro f hf s hs t hst
    have hIndex := hNoGlue _ (hED f hf s hs)
    change (w.limit.edgePartition f).blockCard ((w.limit.edgePartition f).repr s) = 1 at hIndex
    have hBlock := (w.limit.edgePartition f).block_eq_of_rel
      ((w.limit.edgePartition f).rel_repr_right s)
    unfold SheetPartition.blockCard at hIndex
    rw [← hBlock] at hIndex
    have hSingle := (w.limit.edgePartition f).block_eq_singleton_of_blockCard_eq_one s hIndex
    have hMem := ((w.limit.edgePartition f).mem_block_iff s t).mpr hst
    rw [hSingle, Finset.mem_singleton] at hMem
    exact hMem

/-- **Realigning one wall occurrence's permutation.**  A limit isomorphism into a regrowth's
limit can be followed by a pendant automorphism on the branch of one wall occurrence `t`, which
changes nothing else on the wall's star and turns `t`'s permutation into any prescribed `ρ`
that agrees with the old one off the dangling sheets of active wall classes, and moves those
sheets inside their wall class and onto dangling sheets of active classes. -/
theorem exists_realign {T₁ : CFGraph} {first : GluingDatum T₁ degree}
    (w : Regrowth core y degree)
    (hForest : ContractionForest w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
      (w.frame.edgeOf w.column))
    (hNoGlue : DanglingEdgeNoGlue w.limit)
    (ψ : GeometricDatumIso first w.limit) (t : T₁.edges)
    (ht : ψ.targetEdge t ∈ GluingDatum.incidentEdges (mergeVertex w))
    (ρ : Equiv.Perm (Fin degree))
    (hFix : ∀ s, ¬ (0 < nonDanglingValency w.limit
        (w.limit.sourceEndpoint (mergeVertex w) (ψ.edgePerm t s)) ∧
      IsDangling w.limit (w.limit.sourceEdge (ψ.targetEdge t) (ψ.edgePerm t s))) →
        ρ s = ψ.edgePerm t s)
    (hMove : ∀ s, (0 < nonDanglingValency w.limit
        (w.limit.sourceEndpoint (mergeVertex w) (ψ.edgePerm t s)) ∧
      IsDangling w.limit (w.limit.sourceEdge (ψ.targetEdge t) (ψ.edgePerm t s))) →
        (w.limit.vertexPartition (mergeVertex w)).Rel (ρ s) (ψ.edgePerm t s)) :
    ∃ ψ' : GeometricDatumIso first w.limit,
      (∀ e, ψ'.targetEdge e = ψ.targetEdge e) ∧ (∀ v, ψ'.targetVertex v = ψ.targetVertex v) ∧
      (∀ v, ψ.targetVertex v = mergeVertex w → ψ'.vertexPerm v = ψ.vertexPerm v) ∧
      (∀ e, ψ.targetEdge e ∈ GluingDatum.incidentEdges (mergeVertex w) →
        ψ.targetEdge e ≠ ψ.targetEdge t → ψ'.edgePerm e = ψ.edgePerm e) ∧
      ψ'.edgePerm t = ρ := by
  classical
  have hIncX := ends_of_mem ht
  set σ := ψ.edgePerm t
  set D : Fin degree → Prop := fun u ↦
    0 < nonDanglingValency w.limit (w.limit.sourceEndpoint (mergeVertex w) u) ∧
      IsDangling w.limit (w.limit.sourceEdge (ψ.targetEdge t) u)
  have hPend := pendant_of_active w hForest hNoGlue hIncX D (fun s hs ↦ hs.1) (fun s hs ↦ hs.2)
  set π : Equiv.Perm (Fin degree) := σ.symm.trans ρ
  have hπ : ∀ u, ¬ D u → π u = u := by
    intro u hu
    change ρ (σ.symm u) = u
    have := hFix (σ.symm u) (by rw [Equiv.apply_symm_apply]; exact hu)
    rw [this, Equiv.apply_symm_apply]
  have hW : ∀ u, D u → (w.limit.vertexPartition (mergeVertex w)).Rel (π u) u := by
    intro u hu
    change (w.limit.vertexPartition (mergeVertex w)).Rel (ρ (σ.symm u)) u
    have := hMove (σ.symm u) (by rw [Equiv.apply_symm_apply]; exact hu)
    rwa [Equiv.apply_symm_apply] at this
  set θ := pendantIsoW hPend π hπ hW
  refine ⟨ψ.trans θ, fun _ ↦ rfl, fun _ ↦ rfl, fun v hv ↦ ?_, fun e he hne ↦ ?_, ?_⟩
  · refine Equiv.ext fun s ↦ ?_
    change branchPerm (vertexMoved (mergeVertex w) (farEnd (mergeVertex w) (ψ.targetEdge t))
      (farEnd_ne hIncX) (ψ.targetVertex v)) π (ψ.vertexPerm v s) = ψ.vertexPerm v s
    rw [hv, vertexMoved_wall]
    rfl
  · refine Equiv.ext fun s ↦ ?_
    change branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) (ψ.targetEdge t))
      (farEnd_ne hIncX) (ψ.targetEdge e)) π (ψ.edgePerm e s) = ψ.edgePerm e s
    rw [edgeMoved_other (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w)
      hIncX (ends_of_mem he) hne]
    rfl
  · refine Equiv.ext fun s ↦ ?_
    change branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) (ψ.targetEdge t))
      (farEnd_ne hIncX) (ψ.targetEdge t)) π (σ s) = ρ s
    rw [edgeMoved_self hIncX]
    change ρ (σ.symm (σ s)) = ρ s
    rw [Equiv.symm_apply_apply]

end Realign

/-! ## 3.  The transport of two resolutions of "one special class plus singletons" shape -/

section Transport

open ResolutionExpansionFree
open ResolutionM11 (LocalResolution)
open W3Nd2StarExhaustionProof (edgePerm_agree agree_symm_apply incident_iff)

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (ψ : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  (hWall : ψ.targetVertex wall = wall')

/-- **The shape of a valency-four incoming resolution, as relations**: each of the two
endpoint partitions is its own set of active sheets (one class per wall class) plus
singletons, and the regrown occurrence is the set of sheets active at both ends, likewise.

This is a relation shaper; it is produced at every valency-four anchored regrowth and every
placement by `resShape`, and consumed by `transportFree_of_shape` and `exists_transport`. -/
structure ResShape (W : SheetPartition degree) (res : LocalResolution degree)
    (actL actR : Fin degree → Prop) : Prop where
  left : ∀ s t, res.left.Rel s t ↔ s = t ∨ (W.Rel s t ∧ actL s ∧ actL t)
  right : ∀ s t, res.right.Rel s t ↔ s = t ∨ (W.Rel s t ∧ actR s ∧ actR t)
  newEdge : ∀ s t, res.newEdge.Rel s t ↔
    s = t ∨ (W.Rel s t ∧ (actL s ∧ actR s) ∧ (actL t ∧ actR t))

include hWall in
/-- **The transport, from one wall permutation `τ`.**  If `τ` agrees with the wall permutation
modulo the wall partition, carries the two activity sets onto the other resolution's, and
every wall occurrence's permutation agrees with `τ` on the sheets inactive at its end and
carries the active ones to active ones, the two resolutions are transported. -/
theorem transportFree_of_shape (right : target₁.edges → Bool) (right' : target₂.edges → Bool)
    (hSide : ∀ e, right' (ψ.targetEdge e) = right e)
    (res res' : LocalResolution degree) (actL actR : Fin degree → Prop)
    (actL' actR' : Fin degree → Prop)
    (H : ResShape (first.vertexPartition wall) res actL actR)
    (H' : ResShape (second.vertexPartition wall') res' actL' actR')
    (τ : Equiv.Perm (Fin degree))
    (hτW : ∀ s, (first.vertexPartition wall).Rel ((ψ.vertexPerm wall).symm (τ s)) s)
    (hτL : ∀ s, actL' (τ s) ↔ actL s) (hτR : ∀ s, actR' (τ s) ↔ actR s)
    (hEndL : ∀ e : target₁.edges, ((e : target₁.V × target₁.V).1 = wall ∨ (e : target₁.V × target₁.V).2 = wall) →
      right e = false → ∀ s, (¬ actL s → ψ.edgePerm e s = τ s) ∧
        (actL s → actL' (ψ.edgePerm e s)))
    (hEndR : ∀ e : target₁.edges, ((e : target₁.V × target₁.V).1 = wall ∨ (e : target₁.V × target₁.V).2 = wall) →
      right e = true → ∀ s, (¬ actR s → ψ.edgePerm e s = τ s) ∧
        (actR s → actR' (ψ.edgePerm e s))) :
    Nonempty (TransportFree ψ wall wall' right right' res res') := by
  set W := first.vertexPartition wall
  have hWτ := M11StarExhaustionProof.wall_rel_iff_of_agree ψ hWall τ hτW
  have hLref : res.left.Refines W := fun s t h ↦ by
    rcases (H.left s t).mp h with rfl | h
    · rfl
    · exact h.1
  have hRref : res.right.Refines W := fun s t h ↦ by
    rcases (H.right s t).mp h with rfl | h
    · rfl
    · exact h.1
  have hτinj : ∀ a b, a = b ↔ τ a = τ b := fun a b ↦ ⟨fun h ↦ h ▸ rfl, fun h ↦ τ.injective h⟩
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel ψ wall wall' right right' res res'
    hWall hSide hLref hRref τ τ τ hτW hτW ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    rw [H.left, H'.left, hτinj, hWτ, hτL, hτL]
  · intro a b
    rw [H.right, H'.right, hτinj, hWτ, hτR, hτR]
  · intro a b
    rw [H.newEdge, H'.newEdge, hτinj, hWτ, hτL, hτL, hτR, hτR]
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro e hInc s
    have hInc' : ψ.targetEdge e ∈ GluingDatum.incidentEdges wall' :=
      (incident_iff ψ hWall e).mp hInc
    have hAg : W.Rel (τ.symm (ψ.edgePerm e s)) s :=
      agree_symm_apply ψ τ (ψ.edgePerm e) hτW (edgePerm_agree ψ hWall e hInc') s
    by_cases hr : right e = true
    · rw [if_pos hr, if_pos hr, H.right]
      obtain ⟨h1, h2⟩ := hEndR e hInc hr s
      by_cases ha : actR s
      · refine Or.inr ⟨hAg, ?_, ha⟩
        have := h2 ha
        rw [← hτR, Equiv.apply_symm_apply]
        exact this
      · left
        rw [h1 ha, Equiv.symm_apply_apply]
    · have hr' : right e = false := by simpa using hr
      rw [if_neg hr, if_neg hr, H.left]
      obtain ⟨h1, h2⟩ := hEndL e hInc hr' s
      by_cases ha : actL s
      · refine Or.inr ⟨hAg, ?_, ha⟩
        have := h2 ha
        rw [← hτL, Equiv.apply_symm_apply]
        exact this
      · left
        rw [h1 ha, Equiv.symm_apply_apply]

end Transport

/-! ## 4.  The incoming resolution at a change-free wall, on every merged class -/

section Incoming

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)

/-- A sheet is **active at an end** when the incoming source vertex there has a surviving
occurrence.

This is an abbreviation (`nonDanglingValency ≠ 0` at the sheet's endpoint), decidable, and
used throughout §§4--15; both values occur (a bridge's sheets are active at both ends,
`cnt_both_eq_index`; an inactive class is a single sheet, `eq_of_limit_inactive`). -/
def Act (u : target.V) (s : Fin degree) : Prop := nonDanglingValency data (data.sourceEndpoint u s) ≠ 0

noncomputable instance (u : target.V) : DecidablePred (Act data u) := fun s ↦ by unfold Act; infer_instance

theorem refines_merged {u : target.V} (hu : u = a ∨ u = b) :
    (data.vertexPartition u).Refines (mergedPartition data a b) := by
  rcases hu with rfl | rfl
  · exact vertexPartition_refines_mergedPartition data _ _
  · exact vertexPartition_refines_mergedPartition_right data _ _

include hc hab hOne in
/-- The incoming endpoint of a sheet lies over the merged vertex of the sheet's class. -/
theorem sourceVertexMap_endpoint {u : target.V} (hu : u = a ∨ u = b) (s : Fin degree) :
    sourceVertexMap data hc hab hOne (data.sourceEndpoint u s) =
      mergedVertex data hc hab hOne ((mergedPartition data a b).toBlock s) := by
  have h := W4IncomingClassUnion.endpoint_mem_fibre data hc hab hOne
    ((mergedPartition data a b).toBlock s) u hu s
    ((SheetPartition.mem_block_iff _ _ _).mpr ((mergedPartition data a b).rel_repr_left s))
  exact (mem_fibreVertices data hc hab hOne _ _).mp h

include fd hc hab hOne hChangeZero in
/-- **At most one active incoming vertex over each end of a merged class.** -/
theorem endpoint_eq_of_act {u : target.V} (hu : u = a ∨ u = b) {s t : Fin degree}
    (hst : (mergedPartition data a b).Rel s t) (hs : Act data u s) (ht : Act data u t) :
    data.sourceEndpoint u s = data.sourceEndpoint u t := by
  classical
  set blk := (mergedPartition data a b).toBlock s
  have hblk : (mergedPartition data a b).toBlock t = blk := by
    apply Subtype.ext
    exact hst.symm
  have hX : data.sourceEndpoint u s ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne blk) :=
    (mem_activeFibreVertices data hc hab hOne _ _).mpr
      ⟨sourceVertexMap_endpoint data hc hab hOne hu s, hs⟩
  have hY : data.sourceEndpoint u t ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne blk) :=
    (mem_activeFibreVertices data hc hab hOne _ _).mpr
      ⟨(sourceVertexMap_endpoint data hc hab hOne hu t).trans (by rw [hblk]), ht⟩
  rcases W4IncomingPrunedFibre.AnyWall.census data fd hc hab hOne hChangeZero _ ⟨_, hX⟩ with
    ⟨pt, hpt, -⟩ | ⟨e, he, hEnds, -⟩
  · rw [hpt, Finset.mem_singleton] at hX hY
    rw [hX, hY]
  · obtain ⟨h1, h2, -, -, -⟩ := W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hOne _ e
      (by rw [he]; exact Finset.mem_singleton_self e)
    rw [hEnds] at hX hY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
    have hXu : (data.sourceEndpoint u s).1.1 = u := rfl
    have hYu : (data.sourceEndpoint u t).1.1 = u := rfl
    rcases hX with hX | hX <;> rcases hY with hY | hY
    · rw [hX, hY]
    · exfalso; apply hab
      rw [← h1, ← h2, ← hX, ← hY, hXu, hYu]
    · exfalso; apply hab
      rw [← h1, ← h2, ← hX, ← hY, hXu, hYu]
    · rw [hX, hY]

include fd hc hab hOne hChangeZero in
/-- **An endpoint partition is its active sheets plus singletons**, on every merged class. -/
theorem vertex_rel_iff {u : target.V} (hu : u = a ∨ u = b) (s t : Fin degree) :
    (data.vertexPartition u).Rel s t ↔
      s = t ∨ ((mergedPartition data a b).Rel s t ∧ Act data u s ∧ Act data u t) := by
  constructor
  · intro h
    by_cases hs : Act data u s
    · have hEq : data.sourceEndpoint u s = data.sourceEndpoint u t :=
        (data.sourceEndpoint_eq_iff u s _).mpr ⟨rfl, h.trans ((data.vertexPartition u).rel_repr_left t).symm⟩
      refine Or.inr ⟨(refines_merged data hu).rel h, hs, ?_⟩
      unfold Act
      rw [← hEq]
      exact hs
    · left
      have hBlock := W4IncomingClassUnion.AnyWall.inactive_endpoint_block data fd u s
        (by unfold Act at hs; push Not at hs; exact hs)
      have hMem := ((data.vertexPartition u).mem_block_iff s t).mpr h
      rw [hBlock, Finset.mem_singleton] at hMem
      exact hMem.symm
  · rintro (rfl | ⟨hst, hs, ht⟩)
    · rfl
    · have hEq := endpoint_eq_of_act data fd hc hab hOne hChangeZero hu hst hs ht
      have := ((data.sourceEndpoint_eq_iff u s _).mp hEq).2
      exact this.trans ((data.vertexPartition u).rel_repr_left t)

/-- A dangling occurrence has an end of surviving valency zero. -/
theorem end_inactive_of_isDangling {e : data.SourceEdge} (h : IsDangling data e) :
    nonDanglingValency data (data.sourceEnds e).1 = 0 ∨
      nonDanglingValency data (data.sourceEnds e).2 = 0 := by
  rcases h with ⟨⟨cut⟩⟩ | ⟨⟨cut⟩⟩
  · exact Or.inl (DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side data cut
      cut.left_mem)
  · exact Or.inr (DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side data cut
      cut.left_mem)

include hc in
theorem sourceEnds_contracted (s : Fin degree) :
    data.sourceEnds (data.sourceEdge contracted s) =
      (data.sourceEndpoint a s, data.sourceEndpoint b s) := by
  rw [CaterpillarDatum.sourceEnds_sourceEdge, hc]

include hc in
/-- The contracted occurrence of a sheet survives exactly when the sheet is active at both
ends. -/
theorem contracted_survives_iff (s : Fin degree) :
    ¬ IsDangling data (data.sourceEdge contracted s) ↔ Act data a s ∧ Act data b s := by
  have hE := sourceEnds_contracted data hc s
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := ClassInjectivity.nonDanglingValency_ne_zero_of_incident data h
        (Or.inl rfl : Incident data (data.sourceEdge contracted s)
          (data.sourceEnds (data.sourceEdge contracted s)).1)
      rw [hE] at this
      exact this
    · have := ClassInjectivity.nonDanglingValency_ne_zero_of_incident data h
        (Or.inr rfl : Incident data (data.sourceEdge contracted s)
          (data.sourceEnds (data.sourceEdge contracted s)).2)
      rw [hE] at this
      exact this
  · rintro ⟨ha, hb⟩ hD
    rcases end_inactive_of_isDangling data hD with h | h
    · rw [hE] at h; exact ha h
    · rw [hE] at h; exact hb h

include fd hc hab hOne hChangeZero in
/-- **The contracted occurrence's partition is the sheets active at both ends plus
singletons**, on every merged class. -/
theorem contracted_rel_iff (s t : Fin degree) :
    (data.edgePartition contracted).Rel s t ↔
      s = t ∨ ((mergedPartition data a b).Rel s t ∧ (Act data a s ∧ Act data b s) ∧
        (Act data a t ∧ Act data b t)) := by
  classical
  have hRef : (data.edgePartition contracted).Refines (mergedPartition data a b) := by
    have h1 := refines_of_mem_incidentEdges_local data
      (ValencyThreeSplit.contracted_mem_incidentEdges hc (Or.inl rfl))
    exact fun x y hxy ↦ (refines_merged data (Or.inl rfl)).rel (h1.rel hxy)
  have hSame : ∀ x y, (data.edgePartition contracted).Rel x y →
      data.sourceEdge contracted x = data.sourceEdge contracted y := by
    intro x y hxy
    apply Subtype.ext
    exact Prod.ext rfl hxy
  constructor
  · intro h
    by_cases hs : Act data a s ∧ Act data b s
    · refine Or.inr ⟨hRef.rel h, hs, ?_⟩
      have hSurv := (contracted_survives_iff data hc s).mpr hs
      rw [hSame s t h] at hSurv
      exact (contracted_survives_iff data hc t).mp hSurv
    · left
      have hD : IsDangling data (data.sourceEdge contracted s) := by
        by_contra hN
        exact hs ((contracted_survives_iff data hc s).mp hN)
      have hIdx := fd.danglingEdgeNoGlue _ hD
      rw [GluingDatum.sourceEdgeIndex_sourceEdge] at hIdx
      have hBlock := (data.edgePartition contracted).block_eq_singleton_of_blockCard_eq_one s hIdx
      have hMem := ((data.edgePartition contracted).mem_block_iff s t).mpr h
      rw [hBlock, Finset.mem_singleton] at hMem
      exact hMem.symm
  · rintro (rfl | ⟨hst, hs, ht⟩)
    · rfl
    · set blk := (mergedPartition data a b).toBlock s
      have hblk : (mergedPartition data a b).toBlock t = blk := by
        apply Subtype.ext
        exact hst.symm
      have hInt : ∀ x, (mergedPartition data a b).toBlock x = blk → Act data a x ∧ Act data b x →
          data.sourceEdge contracted x ∈ internalEdges data hc hab hOne
            (mergedVertex data hc hab hOne blk) := by
        intro x hx hax
        refine (mem_internalEdges data hc hab hOne _ _).mpr
          ⟨(contracted_survives_iff data hc x).mpr hax, rfl, ?_⟩
        rw [sourceEnds_contracted data hc x, ← hx]
        exact sourceVertexMap_endpoint data hc hab hOne (Or.inl rfl) x
      have hEq := W4IncomingPrunedFibre.AnyWall.internalEdges_subsingleton data fd hc hab hOne
        hChangeZero _ _ (hInt s rfl hs) _ (hInt t hblk ht)
      have h2 := congrArg (fun e : data.SourceEdge ↦ e.1.2) hEq
      exact h2

end Incoming

/-! ## 5.  Boundary survivors of an incoming vertex are the limit survivors on its side -/

section Boundary

open ValencyThreeSplit (ndAt mem_ndAt card_ndAt size ram ram_eq fib intl bdAt mem_bdAt ndOver
  mem_ndOver sum_ndAt_split card_ndAt_split index_le_size sourceEdgeMap_mem_ndAt
  not_mem_incidentEdges_other target_mem_incidentEdges)

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)
  (hCompat : DanglingCompatible data hc hab hOne)

/-- The incoming occurrence under a limit occurrence. -/
noncomputable def liftG (g : (contractDatum data hc hab hOne).SourceEdge) : data.SourceEdge :=
  ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm g).1

theorem liftG_ne (g : (contractDatum data hc hab hOne).SourceEdge) :
    (liftG data hc hab hOne g).1.1 ≠ contracted :=
  ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm g).2

theorem sourceEdgeMap_liftG (g : (contractDatum data hc hab hOne).SourceEdge) :
    sourceEdgeMap data hc hab hOne ⟨liftG data hc hab hOne g, liftG_ne data hc hab hOne g⟩ = g :=
  (ContractionFibre.sourceEdgeEquiv data hc hab hOne).apply_symm_apply g

theorem index_liftG (g : (contractDatum data hc hab hOne).SourceEdge) :
    data.sourceEdgeIndex (liftG data hc hab hOne g) =
      (contractDatum data hc hab hOne).sourceEdgeIndex g :=
  ContractionFibre.sourceEdgeIndex_symm_sourceEdgeEquiv data hc hab hOne g

theorem liftG_injective : Function.Injective (liftG data hc hab hOne) := by
  intro g h hgh
  have h' : ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm g) =
      ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm h) := Subtype.ext hgh
  exact (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm.injective h'

theorem unfold_liftG (g : (contractDatum data hc hab hOne).SourceEdge) :
    unfoldEdge hc hab hOne g.1.1 = (liftG data hc hab hOne g).1.1 := by
  conv_lhs => rw [← sourceEdgeMap_liftG data hc hab hOne g]
  exact unfoldEdge_foldEdge hc hab hOne ⟨_, liftG_ne data hc hab hOne g⟩

/-- The limit survivors of the class of `s` whose target occurrence lies at the end `u`. -/
noncomputable def sideSurv (u : target.V) (s : Fin degree) :
    Finset (contractDatum data hc hab hOne).SourceEdge := by
  classical
  exact (ndAt (contractDatum data hc hab hOne)
    (mergedVertex data hc hab hOne ((mergedPartition data a b).toBlock s))).filter
      fun g ↦ unfoldEdge hc hab hOne g.1.1 ∈ GluingDatum.incidentEdges u

theorem mem_sideSurv (u : target.V) (s : Fin degree) (g : (contractDatum data hc hab hOne).SourceEdge) :
    g ∈ sideSurv data hc hab hOne u s ↔
      g ∈ ndAt (contractDatum data hc hab hOne)
          ((contractDatum data hc hab hOne).sourceEndpoint ⟨a, hab⟩ s) ∧
        unfoldEdge hc hab hOne g.1.1 ∈ GluingDatum.incidentEdges u := by
  classical
  unfold sideSurv
  rw [Finset.mem_filter]
  have h : (contractDatum data hc hab hOne).sourceEndpoint ⟨a, hab⟩ s =
      mergedVertex data hc hab hOne ((mergedPartition data a b).toBlock s) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr s =
        (mergedPartition data a b).repr s
      rw [contractDatum_vertexPartition_merge]
  rw [h]

theorem endpoint_mem_fib {u : target.V} (hu : u = a ∨ u = b) {s : Fin degree}
    (hs : Act data u s) :
    data.sourceEndpoint u s ∈ fib data hc hab hOne ((mergedPartition data a b).toBlock s) :=
  (mem_activeFibreVertices data hc hab hOne _ _).mpr
    ⟨sourceVertexMap_endpoint data hc hab hOne hu s, hs⟩

include fd hChangeZero hCompat in
/-- **The boundary survivors of an active incoming vertex are the lifts of the limit
survivors of its class on its side.** -/
theorem bdAt_eq_image {u : target.V} (hu : u = a ∨ u = b) {s : Fin degree} (hs : Act data u s) :
    bdAt data contracted (data.sourceEndpoint u s) =
      (sideSurv data hc hab hOne u s).image (liftG data hc hab hOne) := by
  classical
  set X := data.sourceEndpoint u s
  have hX := endpoint_mem_fib data hc hab hOne hu hs
  ext e
  rw [Finset.mem_image]
  constructor
  · intro he
    obtain ⟨hnd, hT⟩ := (mem_bdAt data X e).mp he
    refine ⟨sourceEdgeMap data hc hab hOne ⟨e, hT⟩, ?_, ?_⟩
    · unfold sideSurv
      rw [Finset.mem_filter]
      refine ⟨sourceEdgeMap_mem_ndAt hCompat hX he, ?_⟩
      have h1 : unfoldEdge hc hab hOne (sourceEdgeMap data hc hab hOne ⟨e, hT⟩).1.1 = e.1.1 :=
        unfoldEdge_foldEdge hc hab hOne ⟨e.1.1, hT⟩
      rw [h1]
      exact target_mem_incidentEdges data ((mem_ndAt data X e).mp hnd).2
    · change ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm
        (ContractionFibre.sourceEdgeEquiv data hc hab hOne ⟨e, hT⟩)).1 = e
      rw [Equiv.symm_apply_apply]
  · rintro ⟨g, hg, rfl⟩
    unfold sideSurv at hg
    rw [Finset.mem_filter] at hg
    obtain ⟨hgnd, hgu⟩ := hg
    rw [unfold_liftG] at hgu
    set e := liftG data hc hab hOne g
    have hm := (mem_ndAt _ _ _).mp hgnd
    rw [← sourceEdgeMap_liftG data hc hab hOne g] at hm
    obtain ⟨hSurv, hInc⟩ := hm
    have hSurv' : ¬ IsDangling data e := fun hBad ↦
      hSurv (hCompat.1 ⟨_, liftG_ne data hc hab hOne g⟩ hBad)
    unfold Incident at hInc
    rw [sourceEnds_sourceEdgeMap] at hInc
    -- the end of `e` over the class is active and over `u`
    have key : ∀ Y : data.SourceVertex, Incident data e Y →
        sourceVertexMap data hc hab hOne Y =
          mergedVertex data hc hab hOne ((mergedPartition data a b).toBlock s) →
        Y = X := by
      intro Y hYe hYmap
      have hYact : nonDanglingValency data Y ≠ 0 :=
        ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurv' hYe
      have hYfib : Y ∈ fib data hc hab hOne ((mergedPartition data a b).toBlock s) :=
        (mem_activeFibreVertices data hc hab hOne _ _).mpr ⟨hYmap, hYact⟩
      obtain ⟨hYab, hYrepr, -⟩ := (ValencyThreeSplit.mem_fib_iff data hc hab hOne _ Y).mp hYfib
      have hYu : Y.1.1 = u := by
        by_contra hne
        have htY := target_mem_incidentEdges data hYe
        rcases hu with rfl | rfl <;> rcases hYab with h | h
        · exact hne h
        · rw [h] at htY
          exact not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) hgu
            (liftG_ne data hc hab hOne g) htY
        · rw [h] at htY
          exact not_mem_incidentEdges_other hc hab hOne (Or.inr ⟨rfl, rfl⟩) hgu
            (liftG_ne data hc hab hOne g) htY
        · exact hne h
      have hYeq : Y = data.sourceEndpoint u Y.1.2 := by
        rw [← hYu]; exact (data.sourceEndpoint_self Y).symm
      rw [hYeq]
      symm
      apply endpoint_eq_of_act data fd hc hab hOne hChangeZero hu
      · have h1 : (mergedPartition data a b).repr Y.1.2 =
            (mergedPartition data a b).repr s := hYrepr
        exact h1.symm
      · exact hs
      · unfold Act; rw [← hYeq]; exact hYact
    rcases hInc with h | h
    · have hY := key _ (Or.inl rfl) h
      refine (mem_bdAt data X e).mpr ⟨(mem_ndAt data X e).mpr ⟨hSurv', Or.inl hY⟩,
        liftG_ne data hc hab hOne g⟩
    · have hY := key _ (Or.inr rfl) h
      refine (mem_bdAt data X e).mpr ⟨(mem_ndAt data X e).mpr ⟨hSurv', Or.inr hY⟩,
        liftG_ne data hc hab hOne g⟩

include fd hChangeZero hCompat in
theorem card_bdAt_eq {u : target.V} (hu : u = a ∨ u = b) {s : Fin degree} (hs : Act data u s) :
    (bdAt data contracted (data.sourceEndpoint u s)).card = (sideSurv data hc hab hOne u s).card := by
  rw [bdAt_eq_image data fd hc hab hOne hChangeZero hCompat hu hs,
    Finset.card_image_of_injective _ (liftG_injective data hc hab hOne)]

include fd hChangeZero hCompat in
theorem sum_bdAt_eq {u : target.V} (hu : u = a ∨ u = b) {s : Fin degree} (hs : Act data u s) :
    ∑ e ∈ bdAt data contracted (data.sourceEndpoint u s), (data.sourceEdgeIndex e : ℤ) =
      ∑ g ∈ sideSurv data hc hab hOne u s,
        ((contractDatum data hc hab hOne).sourceEdgeIndex g : ℤ) := by
  rw [bdAt_eq_image data fd hc hab hOne hChangeZero hCompat hu hs,
    Finset.sum_image (fun g _ h _ hgh ↦ liftG_injective data hc hab hOne hgh)]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [index_liftG]

end Boundary

/-! ## 6.  The sizes of the three special sets on one class -/

section ClassFacts

/-- **The numerical facts of one merged class**: `xa`, `xb` the numbers of sheets active at
the two ends, `z` the number active at both, `n` the class size, and `Na, Sa, Nb, Sb` the
number and index sum of the limit survivors of the class on each side.

It is produced at every merged class of an incoming cover by `classFacts` /
`classFactsUV`, and consumed by `ClassFacts.eq` (the class counts are determined by the limit
data and, at the anchor, by the bridge index). -/
structure ClassFacts (xa xb z n Na Sa Nb Sb : ℕ) : Prop where
  z_le_a : z ≤ xa
  z_le_b : z ≤ xb
  zero_a : xa = 0 ↔ Na = 0
  zero_b : xb = 0 ↔ Nb = 0
  union : 0 < xa + xb → xa + xb = n + z
  edge : 0 < xa → 0 < xb → 0 < z
  excess_a : 0 < xa → 2 * xa + min z 1 + Na = 2 + z + Sa
  excess_b : 0 < xb → 2 * xb + min z 1 + Nb = 2 + z + Sb
  bound_a : Na = 1 → Sa ≤ xa
  bound_b : Nb = 1 → Sb ≤ xb

/-- **The class sizes are determined by the limit data**, and by `z` at a class with two
limit survivors on each side (the anchor, where `z` is the bridge index `k₁`, fixed by `K`). -/
theorem ClassFacts.eq {xa xb z n Na Sa Nb Sb xa' xb' z' : ℕ}
    (h : ClassFacts xa xb z n Na Sa Nb Sb) (h' : ClassFacts xa' xb' z' n Na Sa Nb Sb)
    (hK : 2 ≤ Na → 2 ≤ Nb → z = z') : xa = xa' ∧ xb = xb' ∧ z = z' := by
  have h1 := h.z_le_a; have h2 := h.z_le_b; have h3 := h.zero_a; have h4 := h.zero_b
  have h5 := h.union; have h6 := h.edge; have h7 := h.excess_a; have h8 := h.excess_b
  have h9 := h.bound_a; have h10 := h.bound_b
  have g1 := h'.z_le_a; have g2 := h'.z_le_b; have g3 := h'.zero_a; have g4 := h'.zero_b
  have g5 := h'.union; have g6 := h'.edge; have g7 := h'.excess_a; have g8 := h'.excess_b
  have g9 := h'.bound_a; have g10 := h'.bound_b
  by_cases hA : Na = 0
  · have hx : xa = 0 := h3.mpr hA
    have hx' : xa' = 0 := g3.mpr hA
    by_cases hB : Nb = 0
    · have hy : xb = 0 := h4.mpr hB
      have hy' : xb' = 0 := g4.mpr hB
      omega
    · have hy : xb ≠ 0 := fun h ↦ hB (h4.mp h)
      have hy' : xb' ≠ 0 := fun h ↦ hB (g4.mp h)
      have := h5 (by omega)
      have := g5 (by omega)
      omega
  · have hx : xa ≠ 0 := fun h ↦ hA (h3.mp h)
    have hx' : xa' ≠ 0 := fun h ↦ hA (g3.mp h)
    by_cases hB : Nb = 0
    · have hy : xb = 0 := h4.mpr hB
      have hy' : xb' = 0 := g4.mpr hB
      have := h5 (by omega)
      have := g5 (by omega)
      omega
    · have hy : xb ≠ 0 := fun h ↦ hB (h4.mp h)
      have hy' : xb' ≠ 0 := fun h ↦ hB (g4.mp h)
      have hz := h6 (by omega) (by omega)
      have hz' := g6 (by omega) (by omega)
      have e1 := h7 (by omega)
      have e2 := h8 (by omega)
      have e3 := g7 (by omega)
      have e4 := g8 (by omega)
      have hzz : z = z' := by
        by_cases hA1 : Na = 1
        · have := h9 hA1
          have := g9 hA1
          omega
        · by_cases hB1 : Nb = 1
          · have := h10 hB1
            have := g10 hB1
            omega
          · exact hK (by omega) (by omega)
      omega

end ClassFacts

/-! ## 7.  The facts of every merged class of an incoming cover -/

section CoverFacts

open ValencyThreeSplit (ndAt mem_ndAt card_ndAt size ram ram_eq fib intl bdAt mem_bdAt ndOver
  mem_ndOver sum_ndAt_split card_ndAt_split index_le_size sourceEdgeMap_mem_ndAt
  not_mem_incidentEdges_other target_mem_incidentEdges)

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)
  (hCompat : DanglingCompatible data hc hab hOne)

/-- The number of sheets of the merged class of `s₀` satisfying `P`. -/
noncomputable def cnt (a b : target.V) (P : Fin degree → Prop) [DecidablePred P] (s₀ : Fin degree) : ℕ :=
  (Finset.univ.filter fun s ↦ (mergedPartition data a b).Rel s₀ s ∧ P s).card

/-- The index sum of the limit survivors of the class of `s` on the side `u`. -/
noncomputable def sideSum (u : target.V) (s : Fin degree) : ℕ :=
  ∑ g ∈ sideSurv data hc hab hOne u s, (contractDatum data hc hab hOne).sourceEdgeIndex g

theorem cnt_congr (P : Fin degree → Prop) [DecidablePred P] {s₀ s₁ : Fin degree}
    (h : (mergedPartition data a b).Rel s₀ s₁) : cnt data a b P s₁ = cnt data a b P s₀ := by
  unfold cnt
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h.trans h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h.symm.trans h1, h2⟩⟩

theorem toBlock_congr {s₀ s₁ : Fin degree} (h : (mergedPartition data a b).Rel s₀ s₁) :
    (mergedPartition data a b).toBlock s₁ = (mergedPartition data a b).toBlock s₀ :=
  Subtype.ext h.symm

theorem sideSurv_congr (u : target.V) {s₀ s₁ : Fin degree}
    (h : (mergedPartition data a b).Rel s₀ s₁) :
    sideSurv data hc hab hOne u s₁ = sideSurv data hc hab hOne u s₀ := by
  unfold sideSurv
  rw [toBlock_congr data h]

include fd hc hab hOne hChangeZero in
/-- The size of an active incoming vertex is the number of sheets of its class active at its
end. -/
theorem size_endpoint {u : target.V} (hu : u = a ∨ u = b) {s₁ : Fin degree}
    (hs : Act data u s₁) : size data (data.sourceEndpoint u s₁) = cnt data a b (Act data u) s₁ := by
  classical
  change (data.vertexPartition u).blockCard ((data.vertexPartition u).repr s₁) = _
  unfold SheetPartition.blockCard cnt
  rw [(data.vertexPartition u).block_eq_of_rel ((data.vertexPartition u).rel_repr_left s₁)]
  congr 1
  ext t
  rw [SheetPartition.mem_block_iff, vertex_rel_iff data fd hc hab hOne hChangeZero hu]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨h1, -, h2⟩)
    · exact ⟨rfl, hs⟩
    · exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr ⟨h1, hs, h2⟩

include fd hc hab hOne hChangeZero in
/-- **The contracted survivor at an active vertex**: present exactly when some sheet of the
class is active at both ends, and then of index `z`. -/
theorem ndOver_facts {u : target.V} (hu : u = a ∨ u = b) {s₁ : Fin degree}
    (hs : Act data u s₁) :
    (ndOver data (data.sourceEndpoint u s₁) contracted).card =
        min (cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₁) 1 ∧
      ∑ e ∈ ndOver data (data.sourceEndpoint u s₁) contracted, (data.sourceEdgeIndex e : ℤ) =
        cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₁ := by
  classical
  set X := data.sourceEndpoint u s₁
  set z := cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₁
  -- the index of a surviving contracted occurrence of the class
  have hIdx : ∀ s₂, (mergedPartition data a b).Rel s₁ s₂ → Act data a s₂ ∧ Act data b s₂ →
      data.sourceEdgeIndex (data.sourceEdge contracted s₂) = z := by
    intro s₂ h12 h2
    rw [GluingDatum.sourceEdgeIndex_sourceEdge]
    unfold SheetPartition.blockCard
    unfold z cnt
    congr 1
    ext t
    rw [SheetPartition.mem_block_iff, contracted_rel_iff data fd hc hab hOne hChangeZero]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨h1, -, h3⟩)
      · exact ⟨h12, h2⟩
      · exact ⟨h12.trans h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact Or.inr ⟨h12.symm.trans h1, h2, h3⟩
  by_cases hz : ∃ s₂, (mergedPartition data a b).Rel s₁ s₂ ∧ Act data a s₂ ∧ Act data b s₂
  · obtain ⟨s₂, h12, h2a, h2b⟩ := hz
    set f := data.sourceEdge contracted s₂
    have hfS : ¬ IsDangling data f := (contracted_survives_iff data hc s₂).mpr ⟨h2a, h2b⟩
    have hfX : Incident data f X := by
      have hE := sourceEnds_contracted data hc s₂
      have hEq : data.sourceEndpoint u s₂ = X := by
        symm
        apply endpoint_eq_of_act data fd hc hab hOne hChangeZero hu h12 hs
        rcases hu with rfl | rfl
        · exact h2a
        · exact h2b
      rcases hu with rfl | rfl
      · left; rw [hE]; exact hEq
      · right; rw [hE]; exact hEq
    have hSing : ndOver data X contracted = {f} := by
      ext g
      rw [mem_ndOver, Finset.mem_singleton]
      constructor
      · rintro ⟨hg, hgT⟩
        obtain ⟨hgS, hgI⟩ := (mem_ndAt data X g).mp hg
        exact W4IncomingPrunedFibre.AnyWall.contracted_sourceEdge_eq_of_incident data fd hc
          hChangeZero X g f hgT rfl hgS hfS hgI hfX
      · rintro rfl
        exact ⟨(mem_ndAt data X _).mpr ⟨hfS, hfX⟩, rfl⟩
    have hzpos : 0 < z := by
      unfold z cnt
      exact Finset.card_pos.mpr ⟨s₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12, h2a, h2b⟩⟩
    rw [hSing, Finset.card_singleton, Finset.sum_singleton, hIdx s₂ h12 ⟨h2a, h2b⟩]
    exact ⟨by omega, rfl⟩
  · have hz0 : z = 0 := by
      unfold z cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hx
      exact hz ⟨x, hx.1, hx.2⟩
    have hEmpty : ndOver data X contracted = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro g hg
      obtain ⟨hg, hgT⟩ := (mem_ndOver data X contracted g).mp hg
      obtain ⟨hgS, hgI⟩ := (mem_ndAt data X g).mp hg
      have hgE : g = data.sourceEdge contracted g.1.2 := by
        apply Subtype.ext
        refine Prod.ext hgT ?_
        have h2 : (data.edgePartition g.1.1).repr g.1.2 = g.1.2 := g.2
        rw [hgT] at h2
        exact h2.symm
      rw [hgE] at hgS hgI
      obtain ⟨h2a, h2b⟩ := (contracted_survives_iff data hc g.1.2).mp hgS
      apply hz
      refine ⟨g.1.2, ?_, h2a, h2b⟩
      have hE := sourceEnds_contracted data hc g.1.2
      have hEnd : data.sourceEndpoint u g.1.2 = X := by
        rcases hgI with h | h <;> rw [hE] at h
        · rcases hu with rfl | rfl
          · exact h
          · exfalso; apply hab
            have := congrArg (fun v : data.SourceVertex ↦ v.1.1) h
            exact this
        · rcases hu with rfl | rfl
          · exfalso; apply hab
            have := congrArg (fun v : data.SourceVertex ↦ v.1.1) h
            exact this.symm
          · exact h
      have := ((data.sourceEndpoint_eq_iff u g.1.2 X).mp hEnd).2
      have hRel : (data.vertexPartition u).Rel s₁ g.1.2 :=
        ((data.vertexPartition u).rel_repr_right s₁).trans this.symm
      exact (refines_merged data hu).rel hRel
    rw [hEmpty, hz0]
    simp

include fd hc hab hOne hChangeZero hCompat in
/-- **The excess formula at an active incoming vertex**, in class counts. -/
theorem excess_count {u : target.V} (hu : u = a ∨ u = b) {s₁ : Fin degree}
    (hs : Act data u s₁) :
    2 * cnt data a b (Act data u) s₁ + min (cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₁) 1
        + (sideSurv data hc hab hOne u s₁).card =
      2 + cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₁ + sideSum data hc hab hOne u s₁ := by
  classical
  set X := data.sourceEndpoint u s₁
  have hram : ram data X = 0 :=
    W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd X (hChangeZero u hu)
  have h := ram_eq data fd.danglingEdgeNoGlue X
  rw [hram, card_ndAt_split data (contracted := contracted) X,
    sum_ndAt_split data (contracted := contracted) X] at h
  obtain ⟨h1, h2⟩ := ndOver_facts data fd hc hab hOne hChangeZero hu hs
  rw [h1, h2, card_bdAt_eq data fd hc hab hOne hChangeZero hCompat hu hs,
    sum_bdAt_eq data fd hc hab hOne hChangeZero hCompat hu hs,
    size_endpoint data fd hc hab hOne hChangeZero hu hs] at h
  have hcast : ((sideSum data hc hab hOne u s₁ : ℕ) : ℤ) =
      ∑ g ∈ sideSurv data hc hab hOne u s₁,
        ((contractDatum data hc hab hOne).sourceEdgeIndex g : ℤ) := by
    unfold sideSum; push_cast; rfl
  zify
  push_cast at h
  rw [hcast]
  linarith

omit [Fintype coordinate] [DecidableEq coordinate] in
include hc hab hOne hChangeZero hCompat in
/-- A limit survivor of a class on a side has, in the incoming cover, an active vertex of the
class at that end. -/
theorem exists_act_of_sideSurv {u : target.V} (hu : u = a ∨ u = b) {s₀ : Fin degree}
    {g : (contractDatum data hc hab hOne).SourceEdge} (hg : g ∈ sideSurv data hc hab hOne u s₀) :
    ∃ s₁, (mergedPartition data a b).Rel s₀ s₁ ∧ Act data u s₁ := by
  classical
  unfold sideSurv at hg
  rw [Finset.mem_filter] at hg
  obtain ⟨hgnd, hgu⟩ := hg
  rw [unfold_liftG] at hgu
  set e := liftG data hc hab hOne g
  have hm := (mem_ndAt _ _ _).mp hgnd
  rw [← sourceEdgeMap_liftG data hc hab hOne g] at hm
  obtain ⟨hSurv, hInc⟩ := hm
  have hSurv' : ¬ IsDangling data e := fun hBad ↦
    hSurv (hCompat.1 ⟨_, liftG_ne data hc hab hOne g⟩ hBad)
  unfold Incident at hInc
  rw [sourceEnds_sourceEdgeMap] at hInc
  have key : ∀ Y : data.SourceVertex, Incident data e Y →
      sourceVertexMap data hc hab hOne Y =
        mergedVertex data hc hab hOne ((mergedPartition data a b).toBlock s₀) →
      ∃ s₁, (mergedPartition data a b).Rel s₀ s₁ ∧ Act data u s₁ := by
    intro Y hYe hYmap
    have hYact : nonDanglingValency data Y ≠ 0 :=
      ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurv' hYe
    have hYfib : Y ∈ fib data hc hab hOne ((mergedPartition data a b).toBlock s₀) :=
      (mem_activeFibreVertices data hc hab hOne _ _).mpr ⟨hYmap, hYact⟩
    obtain ⟨hYab, hYrepr, -⟩ := (ValencyThreeSplit.mem_fib_iff data hc hab hOne _ Y).mp hYfib
    have hYu : Y.1.1 = u := by
      by_contra hne
      have htY := target_mem_incidentEdges data hYe
      rcases hu with rfl | rfl <;> rcases hYab with h | h
      · exact hne h
      · rw [h] at htY
        exact not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) hgu
          (liftG_ne data hc hab hOne g) htY
      · rw [h] at htY
        exact not_mem_incidentEdges_other hc hab hOne (Or.inr ⟨rfl, rfl⟩) hgu
          (liftG_ne data hc hab hOne g) htY
      · exact hne h
    have hYeq : Y = data.sourceEndpoint u Y.1.2 := by
      rw [← hYu]; exact (data.sourceEndpoint_self Y).symm
    refine ⟨Y.1.2, ?_, ?_⟩
    · have h1 : (mergedPartition data a b).repr Y.1.2 = (mergedPartition data a b).repr s₀ :=
        hYrepr
      exact h1.symm
    · unfold Act; rw [← hYeq]; exact hYact
  rcases hInc with h | h
  · exact key _ (Or.inl rfl) h
  · exact key _ (Or.inr rfl) h

include fd hc hab hOne hChangeZero hCompat in
/-- **The facts of one merged class.** -/
theorem classFacts (s₀ : Fin degree) :
    ClassFacts (cnt data a b (Act data a) s₀) (cnt data a b (Act data b) s₀)
      (cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₀) (cnt data a b (fun _ ↦ True) s₀)
      (sideSurv data hc hab hOne a s₀).card (sideSum data hc hab hOne a s₀)
      (sideSurv data hc hab hOne b s₀).card (sideSum data hc hab hOne b s₀) := by
  classical
  set M := mergedPartition data a b
  -- an active sheet of the class, at either end, from a positive count
  have hPos : ∀ (P : Fin degree → Prop) [DecidablePred P], 0 < cnt data a b P s₀ →
      ∃ s₁, M.Rel s₀ s₁ ∧ P s₁ := by
    intro P _ h
    obtain ⟨s₁, hs₁⟩ := Finset.card_pos.mp h
    rw [Finset.mem_filter] at hs₁
    exact ⟨s₁, hs₁.2⟩
  have hPos' : ∀ (P : Fin degree → Prop) [DecidablePred P] (s₁ : Fin degree), M.Rel s₀ s₁ →
      P s₁ → 0 < cnt data a b P s₀ := by
    intro P _ s₁ h1 h2
    exact Finset.card_pos.mpr ⟨s₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
  have hLe : ∀ (P Q : Fin degree → Prop) [DecidablePred P] [DecidablePred Q],
      (∀ s, P s → Q s) → cnt data a b P s₀ ≤ cnt data a b Q s₀ := by
    intro P Q _ _ hPQ
    unfold cnt
    exact Finset.card_le_card (Finset.monotone_filter_right _ fun s _ h ↦ ⟨h.1, hPQ s h.2⟩)
  -- facts at an active sheet, moved to `s₀`
  have hExc : ∀ {u : target.V}, (u = a ∨ u = b) → 0 < cnt data a b (Act data u) s₀ →
      2 * cnt data a b (Act data u) s₀ +
          min (cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₀) 1 +
          (sideSurv data hc hab hOne u s₀).card =
        2 + cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₀ +
          sideSum data hc hab hOne u s₀ := by
    intro u hu h
    obtain ⟨s₁, h01, h1⟩ := hPos _ h
    have := excess_count data fd hc hab hOne hChangeZero hCompat hu h1
    rw [cnt_congr data _ h01, cnt_congr data _ h01, sideSurv_congr data hc hab hOne u h01] at this
    unfold sideSum at this ⊢
    rw [sideSurv_congr data hc hab hOne u h01] at this
    exact this
  have hZero : ∀ {u : target.V}, (u = a ∨ u = b) →
      (cnt data a b (Act data u) s₀ = 0 ↔ (sideSurv data hc hab hOne u s₀).card = 0) := by
    intro u hu
    constructor
    · intro h0
      by_contra hne
      obtain ⟨g, hg⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      obtain ⟨s₁, h01, h1⟩ := exists_act_of_sideSurv data hc hab hOne hChangeZero hCompat hu hg
      have := hPos' _ s₁ h01 h1
      omega
    · intro h0
      by_contra hne
      obtain ⟨s₁, h01, h1⟩ := hPos _ (Nat.pos_of_ne_zero hne)
      have hnd1 := NonDanglingValency.nonDanglingValency_ne_one data fd.connected
        (data.sourceEndpoint u s₁)
      have hsplit := card_ndAt_split data (contracted := contracted) (data.sourceEndpoint u s₁)
      obtain ⟨hov, -⟩ := ndOver_facts data fd hc hab hOne hChangeZero hu h1
      rw [hov, card_bdAt_eq data fd hc hab hOne hChangeZero hCompat hu h1,
        sideSurv_congr data hc hab hOne u h01, h0] at hsplit
      unfold Act at h1
      omega
  refine ⟨hLe _ _ fun s h ↦ h.1, hLe _ _ fun s h ↦ h.2, hZero (Or.inl rfl), hZero (Or.inr rfl),
    ?_, ?_, hExc (Or.inl rfl), hExc (Or.inr rfl), ?_, ?_⟩
  · -- the class union
    intro h
    have hAct : ∃ s₁ u, (u = a ∨ u = b) ∧ M.Rel s₀ s₁ ∧ Act data u s₁ := by
      by_cases ha : 0 < cnt data a b (Act data a) s₀
      · obtain ⟨s₁, h1, h2⟩ := hPos _ ha
        exact ⟨s₁, a, Or.inl rfl, h1, h2⟩
      · obtain ⟨s₁, h1, h2⟩ := hPos _ (show 0 < cnt data a b (Act data b) s₀ by omega)
        exact ⟨s₁, b, Or.inr rfl, h1, h2⟩
    obtain ⟨s₁, u, hu, h01, h1⟩ := hAct
    have hNe : (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne (M.toBlock s₀))).Nonempty := by
      refine ⟨data.sourceEndpoint u s₁, ?_⟩
      have := endpoint_mem_fib data hc hab hOne hu h1
      rwa [toBlock_congr data h01] at this
    have hEvery : ∀ s, M.Rel s₀ s → Act data a s ∨ Act data b s := by
      intro s hs
      exact W4IncomingClassUnion.AnyWall.endpoint_active data fd hc hab hOne (M.toBlock s₀) hNe s
        ((SheetPartition.mem_block_iff _ _ _).mpr ((M.rel_repr_left s₀).trans hs))
    have hU := Finset.card_union_add_card_inter
      (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ Act data a s)
      (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ Act data b s)
    have hUnion : (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ Act data a s) ∪
        (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ Act data b s) =
        Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ True := by
      ext s
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro hs
        rcases hEvery s hs with h | h
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr ⟨hs, h⟩
    have hInter : (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ Act data a s) ∩
        (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ Act data b s) =
        Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ (Act data a s ∧ Act data b s) := by
      ext s
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [hUnion, hInter] at hU
    change (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ Act data a s).card +
      (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ Act data b s).card =
      (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ True).card +
      (Finset.univ.filter fun s ↦ M.Rel s₀ s ∧ (Act data a s ∧ Act data b s)).card
    omega
  · -- the edge
    intro ha hb
    obtain ⟨s₁, h01, h1⟩ := hPos _ ha
    obtain ⟨s₂, h02, h2⟩ := hPos _ hb
    set blk := M.toBlock s₀
    have hX : data.sourceEndpoint a s₁ ∈ activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne blk) := by
      have := endpoint_mem_fib data hc hab hOne (Or.inl rfl) h1
      rwa [toBlock_congr data h01] at this
    have hY : data.sourceEndpoint b s₂ ∈ activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne blk) := by
      have := endpoint_mem_fib data hc hab hOne (Or.inr rfl) h2
      rwa [toBlock_congr data h02] at this
    rcases W4IncomingPrunedFibre.AnyWall.census data fd hc hab hOne hChangeZero _ ⟨_, hX⟩ with
      ⟨pt, hpt, -⟩ | ⟨e, he, -, -⟩
    · exfalso
      rw [hpt, Finset.mem_singleton] at hX hY
      have := congrArg (fun v : data.SourceVertex ↦ v.1.1) (hX.trans hY.symm)
      exact hab this
    · have heMem : e ∈ internalEdges data hc hab hOne (mergedVertex data hc hab hOne blk) := by
        rw [he]; exact Finset.mem_singleton_self e
      obtain ⟨heS, heT, heMap⟩ := (mem_internalEdges data hc hab hOne _ _).mp heMem
      have hgE : e = data.sourceEdge contracted e.1.2 := by
        apply Subtype.ext
        refine Prod.ext heT ?_
        have h2 : (data.edgePartition e.1.1).repr e.1.2 = e.1.2 := e.2
        rw [heT] at h2
        exact h2.symm
      rw [hgE] at heS heMap
      have hboth := (contracted_survives_iff data hc e.1.2).mp heS
      refine hPos' _ e.1.2 ?_ hboth
      rw [sourceEnds_contracted data hc, sourceVertexMap_endpoint data hc hab hOne (Or.inl rfl)]
        at heMap
      have := congrArg (fun v : (contractDatum data hc hab hOne).SourceVertex ↦ v.1.2) heMap
      exact this.symm
  · -- the bounds
    intro h1
    obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h1
    have hpos : 0 < cnt data a b (Act data a) s₀ := by
      by_contra h0
      have := (hZero (Or.inl rfl)).mp (by omega)
      omega
    obtain ⟨s₁, h01, hs₁⟩ := hPos _ hpos
    have hmem : liftG data hc hab hOne g ∈ bdAt data contracted (data.sourceEndpoint a s₁) := by
      rw [bdAt_eq_image data fd hc hab hOne hChangeZero hCompat (Or.inl rfl) hs₁,
        sideSurv_congr data hc hab hOne a h01, hg]
      simp
    have := index_le_size data ((mem_bdAt data _ _).mp hmem).1
    rw [index_liftG, size_endpoint data fd hc hab hOne hChangeZero (Or.inl rfl) hs₁,
      cnt_congr data _ h01] at this
    unfold sideSum
    rw [hg, Finset.sum_singleton]
    exact_mod_cast this
  · intro h1
    obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h1
    have hpos : 0 < cnt data a b (Act data b) s₀ := by
      by_contra h0
      have := (hZero (Or.inr rfl)).mp (by omega)
      omega
    obtain ⟨s₁, h01, hs₁⟩ := hPos _ hpos
    have hmem : liftG data hc hab hOne g ∈ bdAt data contracted (data.sourceEndpoint b s₁) := by
      rw [bdAt_eq_image data fd hc hab hOne hChangeZero hCompat (Or.inr rfl) hs₁,
        sideSurv_congr data hc hab hOne b h01, hg]
      simp
    have := index_le_size data ((mem_bdAt data _ _).mp hmem).1
    rw [index_liftG, size_endpoint data fd hc hab hOne hChangeZero (Or.inr rfl) hs₁,
      cnt_congr data _ h01] at this
    unfold sideSum
    rw [hg, Finset.sum_singleton]
    exact_mod_cast this

end CoverFacts

/-! ## 8.  A regrowth's incoming resolution has the shape -/

section RegrowthShape

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open W4WallExhaustion (mergeVertex)
open ValencyThreeRigidity (IsPlacement resolutionOf endA endB)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The incoming side assignment agrees with a placement on the wall.

It selects the branch of `resolution_facts` / `resShape`; it holds for the incoming side
assignment itself (used in `frameClass_eq_of_reads4`) and fails for its negation there. -/
def Agrees (w : Regrowth core y degree) (second : (w.frame.limitTarget w.column).edges → Bool) :
    Prop :=
  ∀ edge ∈ GluingDatum.incidentEdges (target := w.frame.limitTarget w.column) (mergeVertex w),
    IncomingTargetExpansion.right rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) edge = second edge

/-- **The incoming resolution at a placement**: the regrown occurrence is the contracted
occurrence's partition, and the two endpoints are the two original endpoint partitions, in the
placement's order. -/
theorem resolution_facts (w : Regrowth core y degree)
    (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second) :
    (resolutionOf w second h).newEdge = w.frame.data.edgePartition (w.frame.edgeOf w.column) ∧
      (Agrees w second → (resolutionOf w second h).left = w.frame.data.vertexPartition (endA w) ∧
        (resolutionOf w second h).right = w.frame.data.vertexPartition (endB w)) ∧
      (¬ Agrees w second →
        (resolutionOf w second h).left = w.frame.data.vertexPartition (endB w) ∧
        (resolutionOf w second h).right = w.frame.data.vertexPartition (endA w)) := by
  have hpair := M11IncomingOuterPartitions.transported_endpointPartitions w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) second h
  have hnew := M11IncomingOuterPartitions.transported_edgePartition_new w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) second h
    w.frame.fullDim.targetConnected w.frame.fullDim.targetGenus
  refine ⟨hnew, fun hA ↦ ?_, fun hA ↦ ?_⟩
  · split_ifs at hpair with hh
    · exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
    · exact absurd hA hh
  · split_ifs at hpair with hh
    · exact absurd hh hA
    · exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem limit_wall_partition (w : Regrowth core y degree) :
    w.limit.vertexPartition (mergeVertex w) = mergedPartition w.frame.data (endA w) (endB w) :=
  contractDatum_vertexPartition_merge w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column)

theorem wall_rel_iff_merged (w : Regrowth core y degree) (s t : Fin degree) :
    (w.limit.vertexPartition (mergeVertex w)).Rel s t ↔
      (mergedPartition w.frame.data (endA w) (endB w)).Rel s t := by
  have h : w.limit.vertexPartition (mergeVertex w) =
      mergedPartition w.frame.data (endA w) (endB w) :=
    contractDatum_vertexPartition_merge w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column)
  rw [h]

/-- **The shape of a regrowth's incoming resolution at a valency-four wall**, at any
placement, in the placement's order. -/
theorem resShape (w : Regrowth core y degree) {block}
    (H : ValencyFourSplit.RegrowthAnchor4 w block)
    (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second) :
    (Agrees w second → ResShape (w.limit.vertexPartition (mergeVertex w)) (resolutionOf w second h)
      (Act w.frame.data (endA w)) (Act w.frame.data (endB w))) ∧
    (¬ Agrees w second → ResShape (w.limit.vertexPartition (mergeVertex w))
      (resolutionOf w second h) (Act w.frame.data (endB w)) (Act w.frame.data (endA w))) := by
  obtain ⟨hN, hA, hB⟩ := resolution_facts w second h
  have hCZ := H.changeZero w.frame.fullDim
  have hVa := vertex_rel_iff w.frame.data w.frame.fullDim rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) hCZ (u := endA w) (Or.inl rfl)
  have hVb := vertex_rel_iff w.frame.data w.frame.fullDim rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) hCZ (u := endB w) (Or.inr rfl)
  have hE := contracted_rel_iff w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) hCZ
  refine ⟨fun hag ↦ ⟨fun s t ↦ ?_, fun s t ↦ ?_, fun s t ↦ ?_⟩,
    fun hag ↦ ⟨fun s t ↦ ?_, fun s t ↦ ?_, fun s t ↦ ?_⟩⟩
  · rw [(hA hag).1, hVa, wall_rel_iff_merged]
  · rw [(hA hag).2, hVb, wall_rel_iff_merged]
  · rw [hN, hE, wall_rel_iff_merged]
  · rw [(hB hag).1, hVb, wall_rel_iff_merged]
  · rw [(hB hag).2, hVa, wall_rel_iff_merged]
  · rw [hN, hE, wall_rel_iff_merged, and_comm (a := Act w.frame.data (endA w) s),
      and_comm (a := Act w.frame.data (endA w) t)]

end RegrowthShape

/-! ## 9.  The four labels sit on the four wall occurrences, two at each end -/

section LabelSides

open ValencyFourSplit
open ValencyThreeSplit (ndAt mem_ndAt fib bdAt mem_bdAt limA not_mem_incidentEdges_other
  target_mem_incidentEdges)

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (L : Labelling4 (contractDatum data hc hab hOne) (limA data hc hab hOne block))

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem lift4_eq_liftG (i : Fin 4) : lift4 L i = liftG data hc hab hOne (L.e i) := rfl

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The two branch vertices lie over the two different ends. -/
theorem fib_over_ne (P : Bridge data hc hab hOne block) {X Z : data.SourceVertex}
    (hX : X ∈ fib data hc hab hOne block) (hZ : Z ∈ fib data hc hab hOne block) (hXZ : X ≠ Z) :
    X.1.1 ≠ Z.1.1 := by
  rcases (P.mem_fib_iff' X).mp hX with rfl | rfl <;> rcases (P.mem_fib_iff' Z).mp hZ with rfl | rfl
  · exact absurd rfl hXZ
  · rw [P.fst_over, P.snd_over]; exact hab
  · rw [P.fst_over, P.snd_over]; exact hab.symm
  · exact absurd rfl hXZ

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- **A label sits at a branch vertex exactly when its wall occurrence is at that vertex's
end.** -/
theorem label_side (H : AnchorInput4 data hc hab hOne block) (P : Bridge data hc hab hOne block)
    {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) (j : Fin 4) :
    j ∈ labelsAt L X ↔ unfoldEdge hc hab hOne (L.e j).1.1 ∈ GluingDatum.incidentEdges X.1.1 := by
  rw [unfold_liftG, ← lift4_eq_liftG]
  constructor
  · intro hj
    exact target_mem_incidentEdges data ((mem_ndAt data X _).mp ((mem_labelsAt L X j).mp hj)).2
  · intro hT
    obtain ⟨Z, hZ, hjZ⟩ := exists_mem_labelsAt L H.compat j
    by_cases hZX : Z = X
    · rw [← hZX]; exact hjZ
    · exfalso
      have hTZ := target_mem_incidentEdges data ((mem_ndAt data Z _).mp ((mem_labelsAt L Z j).mp hjZ)).2
      have hne := fib_over_ne P hZ hX hZX
      rcases ValencyFourSplit.over_of_mem_fib hZ with hZa | hZb <;>
        rcases ValencyFourSplit.over_of_mem_fib hX with hXa | hXb
      · exact hne (hZa.trans hXa.symm)
      · rw [hZa] at hTZ; rw [hXb] at hT
        exact not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) hTZ (lift4_ne L j) hT
      · rw [hZb] at hTZ; rw [hXa] at hT
        exact not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) hT (lift4_ne L j) hTZ
      · exact hne (hZb.trans hXb.symm)

include fd in
/-- **The four labels sit on four different wall occurrences.** -/
theorem label_target_injective (H : AnchorInput4 data hc hab hOne block) :
    Function.Injective fun i ↦ (L.e i).1.1 := by
  intro i j hij
  obtain ⟨P⟩ := shape fd H
  simp only at hij
  obtain ⟨X, hX, hi⟩ := exists_mem_labelsAt L H.compat i
  obtain ⟨Z, hZ, hj⟩ := exists_mem_labelsAt L H.compat j
  have hT : (lift4 L i).1.1 = (lift4 L j).1.1 := by
    rw [lift4_eq_liftG, lift4_eq_liftG, ← unfold_liftG, ← unfold_liftG, hij]
  by_cases hXZ : X = Z
  · subst hXZ
    exact lift4_injective L (ValencyThreeSplit.eq_of_ram_zero data fd
      (ram_eq_zero_of_mem_fib fd H hX) ((mem_labelsAt L X i).mp hi)
      ((mem_labelsAt L X j).mp hj) hT)
  · exfalso
    have h1 := (label_side L H P hX i).mp hi
    have h2 := (label_side L H P hZ j).mp hj
    rw [hij] at h1
    have hne := fib_over_ne P hX hZ hXZ
    rcases ValencyFourSplit.over_of_mem_fib hX with hXa | hXb <;>
      rcases ValencyFourSplit.over_of_mem_fib hZ with hZa | hZb
    · exact hne (hXa.trans hZa.symm)
    · rw [hXa] at h1; rw [hZb] at h2
      exact not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) h1
        (by rw [unfold_liftG]; exact lift4_ne L j) h2
    · rw [hXb] at h1; rw [hZa] at h2
      exact not_mem_incidentEdges_other hc hab hOne (Or.inl ⟨rfl, rfl⟩) h2
        (by rw [unfold_liftG]; exact lift4_ne L j) h1
    · exact hne (hXb.trans hZb.symm)

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem label_mem (i : Fin 4) :
    (L.e i).1.1 ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
  target_mem_incidentEdges _ ((mem_ndAt _ _ _).mp (L.mem i)).2

include fd in
/-- **Every wall occurrence carries a label.** -/
theorem exists_label (H : AnchorInput4 data hc hab hOne block) {e : (contract target hab hOne).edges}
    (he : e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩) :
    ∃ i, (L.e i).1.1 = e := by
  classical
  have hsub : Finset.univ.image (fun i ↦ (L.e i).1.1) ⊆
      GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact label_mem L i
  have hcard : (Finset.univ.image (fun i ↦ (L.e i).1.1)).card = 4 := by
    rw [Finset.card_image_of_injective _ (label_target_injective fd L H)]
    simp
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, H.valency])
  rw [← heq] at he
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp he
  exact ⟨i, hi⟩

end LabelSides

/-! ## 10.  The wall permutation `τ` from class counts -/

section Tau

variable {d : ℕ}

open Classical in
/-- Four counts of two predicates on one class, from the three counts and the class size. -/
theorem card_four {α : Type*} [Finite α] (C P Q : α → Prop) (l r : Bool) :
    Nat.card {x // C x ∧ decide (P x) = l ∧ decide (Q x) = r} =
      match l, r with
      | true, true => Nat.card {x // C x ∧ (P x ∧ Q x)}
      | true, false => Nat.card {x // C x ∧ P x} - Nat.card {x // C x ∧ (P x ∧ Q x)}
      | false, true => Nat.card {x // C x ∧ Q x} - Nat.card {x // C x ∧ (P x ∧ Q x)}
      | false, false => Nat.card {x // C x} + Nat.card {x // C x ∧ (P x ∧ Q x)} -
          Nat.card {x // C x ∧ P x} - Nat.card {x // C x ∧ Q x} := by
  classical
  have hPQ := card_and_add_card_and_not Q (fun x ↦ C x ∧ P x)
  have hP := card_and_add_card_and_not P C
  have hnPQ := card_and_add_card_and_not Q (fun x ↦ C x ∧ ¬ P x)
  have e1 : {x // (C x ∧ P x) ∧ Q x} ≃ {x // C x ∧ (P x ∧ Q x)} :=
    Equiv.subtypeEquivRight fun _ ↦ and_assoc
  have hQsplit : Nat.card {x // C x ∧ Q x} =
      Nat.card {x // (C x ∧ P x) ∧ Q x} + Nat.card {x // (C x ∧ ¬ P x) ∧ Q x} := by
    have h := card_and_add_card_and_not P (fun x ↦ C x ∧ Q x)
    have e3 : {x // (C x ∧ Q x) ∧ P x} ≃ {x // (C x ∧ P x) ∧ Q x} :=
      Equiv.subtypeEquivRight fun _ ↦ by tauto
    have e4 : {x // (C x ∧ Q x) ∧ ¬ P x} ≃ {x // (C x ∧ ¬ P x) ∧ Q x} :=
      Equiv.subtypeEquivRight fun _ ↦ by tauto
    rw [Nat.card_congr e3, Nat.card_congr e4] at h
    omega
  rw [Nat.card_congr e1] at hPQ hQsplit
  cases l <;> cases r
  · -- false false
    have : {x // C x ∧ decide (P x) = false ∧ decide (Q x) = false} ≃
        {x // (C x ∧ ¬ P x) ∧ ¬ Q x} := Equiv.subtypeEquivRight fun x ↦ by simp [and_assoc]
    rw [Nat.card_congr this]
    simp only
    omega
  · have : {x // C x ∧ decide (P x) = false ∧ decide (Q x) = true} ≃
        {x // (C x ∧ ¬ P x) ∧ Q x} := Equiv.subtypeEquivRight fun x ↦ by simp [and_assoc]
    rw [Nat.card_congr this]
    simp only
    exact (Nat.sub_eq_of_eq_add' hQsplit).symm
  · have : {x // C x ∧ decide (P x) = true ∧ decide (Q x) = false} ≃
        {x // (C x ∧ P x) ∧ ¬ Q x} := Equiv.subtypeEquivRight fun x ↦ by simp [and_assoc]
    rw [Nat.card_congr this]
    simp only
    omega
  · have : {x // C x ∧ decide (P x) = true ∧ decide (Q x) = true} ≃
        {x // C x ∧ (P x ∧ Q x)} := Equiv.subtypeEquivRight fun x ↦ by simp
    rw [Nat.card_congr this]

/-- **A permutation `τ` agreeing with `ν` modulo the partition and matching two pairs of
activity predicates**, as soon as the counts agree class by class. -/
theorem exists_tau (W W' : SheetPartition d) (ν : Equiv.Perm (Fin d))
    (hν : ∀ s t, W'.Rel (ν s) (ν t) ↔ W.Rel s t) (P Q P' Q' : Fin d → Prop)
    (hT : ∀ s₀, Nat.card {s // W.Rel s₀ s} = Nat.card {u // W'.Rel (ν s₀) u})
    (hP : ∀ s₀, Nat.card {s // W.Rel s₀ s ∧ P s} = Nat.card {u // W'.Rel (ν s₀) u ∧ P' u})
    (hQ : ∀ s₀, Nat.card {s // W.Rel s₀ s ∧ Q s} = Nat.card {u // W'.Rel (ν s₀) u ∧ Q' u})
    (hPQ : ∀ s₀, Nat.card {s // W.Rel s₀ s ∧ (P s ∧ Q s)} =
      Nat.card {u // W'.Rel (ν s₀) u ∧ (P' u ∧ Q' u)}) :
    ∃ τ : Equiv.Perm (Fin d), ∀ s, W'.Rel (τ s) (ν s) ∧ (P' (τ s) ↔ P s) ∧ (Q' (τ s) ↔ Q s) := by
  classical
  let f : Fin d → Fin d × Bool × Bool := fun s ↦ (W'.repr (ν s), decide (P s), decide (Q s))
  let g : Fin d → Fin d × Bool × Bool := fun u ↦ (W'.repr u, decide (P' u), decide (Q' u))
  have hfib : ∀ k, Nat.card {s // f s = k} = Nat.card {u // g u = k} := by
    rintro ⟨c, l, r⟩
    have ef : {s // f s = (c, l, r)} ≃ {s // W'.repr (ν s) = c ∧ decide (P s) = l ∧
        decide (Q s) = r} := Equiv.subtypeEquivRight fun s ↦ by simp [f]
    have eg : {u // g u = (c, l, r)} ≃ {u // W'.repr u = c ∧ decide (P' u) = l ∧
        decide (Q' u) = r} := Equiv.subtypeEquivRight fun u ↦ by simp [g]
    rw [Nat.card_congr ef, Nat.card_congr eg]
    by_cases hc : ∃ s₀, W'.repr (ν s₀) = c
    · obtain ⟨s₀, hs₀⟩ := hc
      have e1 : {s // W'.repr (ν s) = c ∧ decide (P s) = l ∧ decide (Q s) = r} ≃
          {s // W.Rel s₀ s ∧ decide (P s) = l ∧ decide (Q s) = r} :=
        Equiv.subtypeEquivRight fun s ↦ by
          rw [← hν, SheetPartition.Rel, hs₀]
          exact ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
      have e2 : {u // W'.repr u = c ∧ decide (P' u) = l ∧ decide (Q' u) = r} ≃
          {u // W'.Rel (ν s₀) u ∧ decide (P' u) = l ∧ decide (Q' u) = r} :=
        Equiv.subtypeEquivRight fun u ↦ by
          rw [SheetPartition.Rel, hs₀]
          exact ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
      rw [Nat.card_congr e1, Nat.card_congr e2, card_four, card_four]
      cases l <;> cases r <;> simp only [hT s₀, hP s₀, hQ s₀, hPQ s₀]
    · have h1 : IsEmpty {s // W'.repr (ν s) = c ∧ decide (P s) = l ∧ decide (Q s) = r} :=
        ⟨fun x ↦ hc ⟨x.1, x.2.1⟩⟩
      have h2 : IsEmpty {u // W'.repr u = c ∧ decide (P' u) = l ∧ decide (Q' u) = r} :=
        ⟨fun x ↦ hc ⟨ν.symm x.1, by rw [Equiv.apply_symm_apply]; exact x.2.1⟩⟩
      rw [@Nat.card_of_isEmpty _ h1, @Nat.card_of_isEmpty _ h2]
  obtain ⟨τ, hτ⟩ := exists_equiv_fiber f g hfib
  refine ⟨τ, fun s ↦ ?_⟩
  have h := hτ s
  simp only [f, g, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · simpa using h2
  · simpa using h3

end Tau

/-! ## 11.  The realigned occurrence permutation `ρ` -/

section Rho

variable {d : ℕ} {κ : Type*}

/-- **Extending an injective, colour-preserving map on a set to a colour-preserving
permutation**, between two colourings with equal colour classes. -/
theorem exists_perm_extend2 (cls₁ cls₂ : Fin d → κ)
    (hcard : ∀ k, Nat.card {x // cls₁ x = k} = Nat.card {y // cls₂ y = k})
    (P : Fin d → Prop) (f : Fin d → Fin d) (hinj : ∀ x y, P x → P y → f x = f y → x = y)
    (hf : ∀ x, P x → cls₂ (f x) = cls₁ x) :
    ∃ π : Equiv.Perm (Fin d), (∀ x, P x → π x = f x) ∧ ∀ x, cls₂ (π x) = cls₁ x := by
  classical
  let Q : Fin d → Prop := fun y ↦ ∃ x, P x ∧ f x = y
  let g : {x // P x} ≃ {y // Q y} :=
    Equiv.ofBijective (fun x ↦ ⟨f x.1, x.1, x.2, rfl⟩)
      ⟨fun x y h ↦ Subtype.ext (hinj x.1 y.1 x.2 y.2 (congrArg Subtype.val h)),
        fun y ↦ by obtain ⟨x, hx, hxy⟩ := y.2; exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  have hPQ : ∀ k, Nat.card {x // cls₁ x = k ∧ P x} = Nat.card {y // cls₂ y = k ∧ Q y} := by
    intro k
    have e0 : {a : {x // P x} // cls₁ a.1 = k} ≃ {b : {y // Q y} // cls₂ b.1 = k} :=
      g.subtypeEquiv (p := fun a ↦ cls₁ a.1 = k) (q := fun b ↦ cls₂ b.1 = k)
        (fun a ↦ by change _ ↔ cls₂ (f a.1) = k; rw [hf a.1 a.2])
    have e1 : {a : {x // P x} // cls₁ a.1 = k} ≃ {x // cls₁ x = k ∧ P x} :=
      (Equiv.subtypeSubtypeEquivSubtypeInter P (fun x ↦ cls₁ x = k)).trans
        (Equiv.subtypeEquivRight fun _ ↦ and_comm)
    have e2 : {b : {y // Q y} // cls₂ b.1 = k} ≃ {y // cls₂ y = k ∧ Q y} :=
      (Equiv.subtypeSubtypeEquivSubtypeInter Q (fun y ↦ cls₂ y = k)).trans
        (Equiv.subtypeEquivRight fun _ ↦ and_comm)
    exact Nat.card_congr (e1.symm.trans (e0.trans e2))
  have hc : ∀ k, Nat.card {a : {x // ¬ P x} // cls₁ a.1 = k} =
      Nat.card {b : {y // ¬ Q y} // cls₂ b.1 = k} := by
    intro k
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun x ↦ ¬ P x)
      (fun x ↦ cls₁ x = k)),
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun y ↦ ¬ Q y)
      (fun y ↦ cls₂ y = k))]
    have h1 := card_and_add_card_and_not P (fun x ↦ cls₁ x = k)
    have h2 := card_and_add_card_and_not Q (fun y ↦ cls₂ y = k)
    rw [hPQ k, hcard k] at h1
    have e1 : {x // ¬ P x ∧ cls₁ x = k} ≃ {x // cls₁ x = k ∧ ¬ P x} :=
      Equiv.subtypeEquivRight fun _ ↦ and_comm
    have e2 : {x // ¬ Q x ∧ cls₂ x = k} ≃ {x // cls₂ x = k ∧ ¬ Q x} :=
      Equiv.subtypeEquivRight fun _ ↦ and_comm
    rw [Nat.card_congr e1, Nat.card_congr e2]
    omega
  obtain ⟨e, he⟩ := exists_equiv_fiber (fun a : {x // ¬ P x} ↦ cls₁ a.1)
    (fun b : {y // ¬ Q y} ↦ cls₂ b.1) hc
  refine ⟨Equiv.subtypeCongr g e, fun x hx ↦ ?_, fun x ↦ ?_⟩
  · have : Equiv.subtypeCongr g e x = (g ⟨x, hx⟩).1 := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
    rw [this]
    rfl
  · by_cases hx : P x
    · have : Equiv.subtypeCongr g e x = (g ⟨x, hx⟩).1 := by
        simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
      rw [this]; exact hf x hx
    · have : Equiv.subtypeCongr g e x = (e ⟨x, hx⟩).1 := by
        simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
      rw [this]; exact he _

/-- **The realigned permutation of one wall occurrence.**  `σ` is the occurrence's permutation,
`τ` the wall permutation, `act`/`act'` the activity at the occurrence's end, `D'` the sheets of
the second limit that dangle on the occurrence in an active wall class.  If a sheet off `D'`
active on the first side is carried to an active one (`hSurv`), and a sheet off `D'` inactive on
the first side is carried where `τ` carries it (`hInact`), there is `ρ` agreeing with `σ` off
`D'`, preserving the wall classes, agreeing with `τ` on the inactive sheets and carrying active
sheets to active ones. -/
theorem exists_rho (W' : SheetPartition d) (ν σ τ : Equiv.Perm (Fin d))
    (hσ : ∀ s, W'.Rel (σ s) (ν s)) (hτ : ∀ s, W'.Rel (τ s) (ν s))
    (act act' D' : Fin d → Prop) (hτact : ∀ s, act' (τ s) ↔ act s)
    (hSurv : ∀ s, ¬ D' (σ s) → act s → act' (σ s))
    (hInact : ∀ s, ¬ D' (σ s) → ¬ act s → σ s = τ s) :
    ∃ ρ : Equiv.Perm (Fin d), (∀ s, ¬ D' (σ s) → ρ s = σ s) ∧ (∀ s, W'.Rel (ρ s) (ν s)) ∧
      (∀ s, ¬ act s → ρ s = τ s) ∧ (∀ s, act s → act' (ρ s)) := by
  classical
  let P : Fin d → Prop := fun s ↦ ¬ D' (σ s) ∨ ¬ act s
  let f : Fin d → Fin d := fun s ↦ if D' (σ s) then τ s else σ s
  have hinj : ∀ x y, P x → P y → f x = f y → x = y := by
    intro x y hx hy hxy
    simp only [f] at hxy
    by_cases hDx : D' (σ x) <;> by_cases hDy : D' (σ y) <;>
      simp only [hDx, hDy, if_true, if_false] at hxy
    · exact τ.injective hxy
    · -- `x` inactive in `D'`, `y` off `D'`
      have hax : ¬ act x := by rcases hx with h | h; exact absurd hDx h; exact h
      have hay : ¬ act y := by
        intro hay
        have := hSurv y hDy hay
        rw [← hxy, hτact] at this
        exact hax this
      rw [hInact y hDy hay] at hxy
      exact τ.injective hxy
    · have hay : ¬ act y := by rcases hy with h | h; exact absurd hDy h; exact h
      have hax : ¬ act x := by
        intro hax
        have := hSurv x hDx hax
        rw [hxy, hτact] at this
        exact hay this
      rw [hInact x hDx hax] at hxy
      exact τ.injective hxy
    · exact σ.injective hxy
  have hcard : ∀ k, Nat.card {x // W'.repr (ν x) = k} = Nat.card {y // W'.repr y = k} :=
    fun k ↦ Nat.card_congr (ν.subtypeEquiv fun _ ↦ Iff.rfl)
  have hf : ∀ x, P x → W'.repr (f x) = W'.repr (ν x) := by
    intro x _
    simp only [f]
    split_ifs
    · exact hτ x
    · exact hσ x
  obtain ⟨π, hπP, hπc⟩ := exists_perm_extend2 (fun x ↦ W'.repr (ν x)) W'.repr hcard P f hinj hf
  refine ⟨π, fun s hs ↦ ?_, fun s ↦ hπc s, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hπP s (Or.inl hs)]
    simp only [f, if_neg hs]
  · rw [hπP s (Or.inr hs)]
    simp only [f]
    split_ifs with hD
    · rfl
    · exact hInact s hD hs
  · by_cases hD : D' (σ s)
    · -- `π s` is off the image of `P`, hence active
      by_contra hna
      have hs' : ¬ act (τ.symm (π s)) := by
        rw [← hτact, Equiv.apply_symm_apply]; exact hna
      set x := τ.symm (π s)
      have hPx : P x := Or.inr hs'
      have hfx : f x = π s := by
        simp only [f]
        split_ifs with hDx
        · simp [x]
        · rw [hInact x hDx hs']
          simp [x]
      have := hπP x hPx
      rw [hfx] at this
      have hxs : x = s := π.injective this
      rw [hxs] at hs'
      exact hs' hs
    · rw [hπP s (Or.inl hD)]
      simp only [f, if_neg hD]
      exact hSurv s hD hs

end Rho

/-! ## 12.  Limit-level facts along a limit isomorphism -/

section LimitFacts

variable {T₁ T₂ : CFGraph} {degree : ℕ} {first : GluingDatum T₁ degree}
  {second : GluingDatum T₂ degree}

theorem sourceVertexEquiv_sourceEndpoint (ψ : GeometricDatumIso first second) (v : T₁.V)
    (s : Fin degree) :
    ψ.sourceVertexEquiv (first.sourceEndpoint v s) =
      second.sourceEndpoint (ψ.targetVertex v) (ψ.vertexPerm v s) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ψ.vertexPerm v ((first.vertexPartition v).repr s) =
      (second.vertexPartition (ψ.targetVertex v)).repr (ψ.vertexPerm v s)
    rw [ψ.vertexPartition v]
    change _ = ψ.vertexPerm v ((first.vertexPartition v).repr ((ψ.vertexPerm v).symm
      (ψ.vertexPerm v s)))
    rw [Equiv.symm_apply_apply]

theorem wall_rel_map (ψ : GeometricDatumIso first second) (v : T₁.V) (s t : Fin degree) :
    (second.vertexPartition (ψ.targetVertex v)).Rel (ψ.vertexPerm v s) (ψ.vertexPerm v t) ↔
      (first.vertexPartition v).Rel s t := by
  rw [ψ.vertexPartition v, SheetPartition.relabel_rel_iff]

end LimitFacts

section IncomingLimit

open ValencyThreeSplit (ndAt mem_ndAt card_ndAt)

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)
  (hCompat : DanglingCompatible data hc hab hOne)

theorem limit_sourceEndpoint (s : Fin degree) :
    (contractDatum data hc hab hOne).sourceEndpoint ⟨a, hab⟩ s =
      mergedVertex data hc hab hOne ((mergedPartition data a b).toBlock s) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr s =
      (mergedPartition data a b).repr s
    rw [contractDatum_vertexPartition_merge]

/-- The incoming occurrence under a limit wall occurrence at a sheet. -/
theorem liftG_sourceEdge (t : (contract target hab hOne).edges) (s : Fin degree) :
    liftG data hc hab hOne ((contractDatum data hc hab hOne).sourceEdge t s) =
      data.sourceEdge (unfoldEdge hc hab hOne t) s := by
  apply Subtype.ext
  apply Prod.ext
  · rw [← unfold_liftG]; rfl
  · change ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm
      ((contractDatum data hc hab hOne).sourceEdge t s)).1.1.2 =
      (data.edgePartition (unfoldEdge hc hab hOne t)).repr s
    have hmap := sourceEdgeMap_liftG data hc hab hOne ((contractDatum data hc hab hOne).sourceEdge t s)
    have h2 := congrArg (fun g : (contractDatum data hc hab hOne).SourceEdge ↦ g.1.2) hmap
    exact h2.trans (by
      change ((contractDatum data hc hab hOne).edgePartition t).repr s = _
      rw [← foldEdge_unfoldEdge hc hab hOne t (unfoldEdge_ne_contracted hc hab hOne t),
        contractDatum_edgePartition_foldEdge, unfoldEdge_foldEdge])

include hCompat in
/-- **A surviving limit wall occurrence at a sheet makes the sheet active at the
occurrence's end.** -/
theorem act_of_survives {u : target.V} {t : (contract target hab hOne).edges}
    (ht : unfoldEdge hc hab hOne t ∈ GluingDatum.incidentEdges u) {s : Fin degree}
    (h : ¬ IsDangling (contractDatum data hc hab hOne)
      ((contractDatum data hc hab hOne).sourceEdge t s)) : Act data u s := by
  have hS : ¬ IsDangling data (data.sourceEdge (unfoldEdge hc hab hOne t) s) := by
    intro hD
    apply h
    rw [← liftG_sourceEdge data hc hab hOne] at hD
    have := hCompat.1 ⟨_, liftG_ne data hc hab hOne _⟩ hD
    rwa [sourceEdgeMap_liftG] at this
  have hInc : Incident data (data.sourceEdge (unfoldEdge hc hab hOne t) s)
      (data.sourceEndpoint u s) := by
    have hE := CaterpillarDatum.sourceEnds_sourceEdge data (unfoldEdge hc hab hOne t) s
    rcases ValencyThreeResolutionMatch.ends_of_mem ht with h1 | h1
    · left; rw [hE, h1]
    · right; rw [hE, h1]
  exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hS hInc

include fd hc hab hOne hChangeZero hCompat in
/-- **An active sheet lies in an active limit wall class.** -/
theorem limit_active_of_act {u : target.V} (hu : u = a ∨ u = b) {s : Fin degree}
    (hs : Act data u s) :
    0 < nonDanglingValency (contractDatum data hc hab hOne)
      ((contractDatum data hc hab hOne).sourceEndpoint ⟨a, hab⟩ s) := by
  classical
  have hF := classFacts data fd hc hab hOne hChangeZero hCompat s
  have hpos : 0 < cnt data a b (Act data u) s :=
    Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hs⟩⟩
  have hN : 0 < (sideSurv data hc hab hOne u s).card := by
    rcases hu with rfl | rfl
    · have := hF.zero_a; omega
    · have := hF.zero_b; omega
  obtain ⟨g, hg⟩ := Finset.card_pos.mp hN
  have hgnd : g ∈ ndAt (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne ((mergedPartition data a b).toBlock s)) := by
    unfold sideSurv at hg; exact (Finset.mem_filter.mp hg).1
  rw [limit_sourceEndpoint, ← card_ndAt]
  exact Finset.card_pos.mpr ⟨g, hgnd⟩

include fd hc hab hOne hChangeZero in
/-- **An inactive limit wall class is a single sheet.** -/
theorem eq_of_limit_inactive {s : Fin degree}
    (h0 : nonDanglingValency (contractDatum data hc hab hOne)
      ((contractDatum data hc hab hOne).sourceEndpoint ⟨a, hab⟩ s) = 0)
    (hCompat : DanglingCompatible data hc hab hOne) {x : Fin degree}
    (hx : (mergedPartition data a b).Rel s x) : x = s := by
  have hna : ¬ Act data a s := fun h ↦ by
    have := limit_active_of_act data fd hc hab hOne hChangeZero hCompat (Or.inl rfl) h; omega
  have hnb : ¬ Act data b s := fun h ↦ by
    have := limit_active_of_act data fd hc hab hOne hChangeZero hCompat (Or.inr rfl) h; omega
  have hA := W4IncomingClassUnion.AnyWall.inactive_endpoint_block data fd a s
    (by unfold Act at hna; push Not at hna; exact hna)
  have hB := W4IncomingClassUnion.AnyWall.inactive_endpoint_block data fd b s
    (by unfold Act at hnb; push Not at hnb; exact hnb)
  exact (W4IncomingClassUnion.eq_of_join_rel_of_singletons _ _ s x hA hB hx).symm

end IncomingLimit

theorem ClassFacts.swap {xa xb z n Na Sa Nb Sb : ℕ} (h : ClassFacts xa xb z n Na Sa Nb Sb) :
    ClassFacts xb xa z n Nb Sb Na Sa :=
  ⟨h.z_le_b, h.z_le_a, h.zero_b, h.zero_a, fun hp ↦ by have := h.union (by omega); omega,
    fun ha hb ↦ h.edge hb ha, h.excess_b, h.excess_a, h.bound_b, h.bound_a⟩

section CountsUV

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)
  (hCompat : DanglingCompatible data hc hab hOne)

theorem cnt_and_comm (P Q : Fin degree → Prop) [DecidablePred P] [DecidablePred Q]
    (s₀ : Fin degree) :
    cnt data a b (fun s ↦ P s ∧ Q s) s₀ = cnt data a b (fun s ↦ Q s ∧ P s) s₀ := by
  unfold cnt
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm (a := P s)]

include fd hc hab hOne hChangeZero hCompat in
/-- **The facts of a merged class, at an ordered pair of ends.** -/
theorem classFactsUV {u v : target.V} (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (s₀ : Fin degree) :
    ClassFacts (cnt data a b (Act data u) s₀) (cnt data a b (Act data v) s₀)
      (cnt data a b (fun s ↦ Act data u s ∧ Act data v s) s₀) (cnt data a b (fun _ ↦ True) s₀)
      (sideSurv data hc hab hOne u s₀).card (sideSum data hc hab hOne u s₀)
      (sideSurv data hc hab hOne v s₀).card (sideSum data hc hab hOne v s₀) := by
  have h := classFacts data fd hc hab hOne hChangeZero hCompat s₀
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · rw [cnt_and_comm]
    exact h.swap

/-- A class count as a cardinality. -/
theorem cnt_eq_natCard (P : Fin degree → Prop) [DecidablePred P] (s₀ : Fin degree) :
    cnt data a b P s₀ = Nat.card {s // (mergedPartition data a b).Rel s₀ s ∧ P s} := by
  unfold cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end CountsUV

section BridgeCount

open ValencyThreeSplit (ndAt mem_ndAt fib intl mem_fib_iff)

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hChangeZero : ∀ place : target.V, place = a ∨ place = b → data.targetChange place = 0)
  {block : (mergedPartition data a b).Blocks}

include fd hChangeZero in
/-- **At the anchor class, the sheets active at both ends are the sheets of the bridge**: their
number is the bridge index `k₁`. -/
theorem cnt_both_eq_index (P : ValencyFourSplit.Bridge data hc hab hOne block) {s₀ : Fin degree}
    (hs₀ : (mergedPartition data a b).repr s₀ = block.1) :
    cnt data a b (fun s ↦ Act data a s ∧ Act data b s) s₀ = data.sourceEdgeIndex P.e₁ := by
  classical
  have hT := P.e₁_target
  have hrep : (data.edgePartition contracted).repr P.e₁.1.2 = P.e₁.1.2 := by
    have := P.e₁.2
    rw [hT] at this
    exact this
  set r := P.e₁.1.2 with hr
  have hE : data.sourceEdge contracted r = P.e₁ := Subtype.ext (Prod.ext hT.symm hrep)
  have hSurv : ¬ IsDangling data (data.sourceEdge contracted r) := by
    rw [hE]; exact P.e₁_survives
  have hAct := (contracted_survives_iff data hc r).mp hSurv
  have hrel : (mergedPartition data a b).Rel s₀ r := by
    have hX := P.fst_mem
    rw [← hE, sourceEnds_contracted data hc r] at hX
    have h2 := ((mem_fib_iff data hc hab hOne block _).mp hX).2.1
    change (mergedPartition data a b).repr ((data.vertexPartition a).repr r) = block.1 at h2
    have h3 : (mergedPartition data a b).Rel ((data.vertexPartition a).repr r) r :=
      refines_merged data (Or.inl rfl) _ _ ((data.vertexPartition a).rel_repr_left r)
    change (mergedPartition data a b).repr s₀ = (mergedPartition data a b).repr r
    rw [hs₀, ← h2]
    exact h3
  unfold cnt GluingDatum.sourceEdgeIndex SheetPartition.blockCard SheetPartition.block
  rw [hT]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [contracted_rel_iff data fd hc hab hOne hChangeZero]
  constructor
  · rintro ⟨h1, h2⟩
    exact Or.inr ⟨hrel.symm.trans h1, hAct, h2⟩
  · rintro (rfl | ⟨h1, -, h2⟩)
    · exact ⟨hrel, hAct⟩
    · exact ⟨hrel.trans h1, h2⟩

end BridgeCount

/-! ## 13.  Two regrowths at one labelled metric limit: the class invariants correspond -/

section RegrowthCounts

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open W4WallExhaustion (mergeVertex)
open ValencyThreeRigidity (endA endB)
open ValencyThreeSplit (ndAt mem_ndAt card_ndAt target_mem_incidentEdges anchorOf)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The limit survivors of a class of a regrowth, on one side. -/
noncomputable abbrev rSurv (w : Regrowth core y degree) (u : w.frame.target.V) (s : Fin degree) :=
  sideSurv w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    u s

noncomputable abbrev rSum (w : Regrowth core y degree) (u : w.frame.target.V) (s : Fin degree) :=
  sideSum w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    u s

noncomputable abbrev rCnt (w : Regrowth core y degree) (P : Fin degree → Prop) [DecidablePred P]
    (s : Fin degree) : ℕ :=
  cnt w.frame.data (endA w) (endB w) P s

theorem limit_endpoint (w : Regrowth core y degree) (s : Fin degree) :
    w.limit.sourceEndpoint (mergeVertex w) s =
      mergedVertex w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column)
        ((mergedPartition w.frame.data (endA w) (endB w)).toBlock s) :=
  limit_sourceEndpoint w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) s

variable {c₂ : Core n p}

/-- **The side survivors of corresponding classes correspond**, under a limit isomorphism
matching the two placements. -/
theorem rSurv_map (w : Regrowth core y degree) (w' : Regrowth c₂ y degree)
    (ψ : GeometricDatumIso w.limit w'.limit)
    (hWall : ψ.targetVertex (mergeVertex w) = mergeVertex w')
    (second : (w.frame.limitTarget w.column).edges → Bool)
    (second' : (w'.frame.limitTarget w'.column).edges → Bool)
    (hsec : ∀ e, second' (ψ.targetEdge e) = second e)
    (bit : Bool) (u : w.frame.target.V) (u' : w'.frame.target.V)
    (hside : ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), second e = bit ↔
      unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) e ∈
        GluingDatum.incidentEdges u)
    (hside' : ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w'), second' e = bit ↔
      unfoldEdge rfl (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column) e ∈
        GluingDatum.incidentEdges u')
    (s₀ : Fin degree) :
    (rSurv w' u' (ψ.vertexPerm (mergeVertex w) s₀)).card = (rSurv w u s₀).card ∧
      rSum w' u' (ψ.vertexPerm (mergeVertex w) s₀) = rSum w u s₀ := by
  classical
  have hConn := ValencyThreeSplit.connected_limit w
  have hV : ψ.sourceVertexEquiv (w.limit.sourceEndpoint (mergeVertex w) s₀) =
      w'.limit.sourceEndpoint (mergeVertex w') (ψ.vertexPerm (mergeVertex w) s₀) := by
    rw [sourceVertexEquiv_sourceEndpoint, hWall]
  have hWallInc : ∀ g : w.limit.SourceEdge, Incident w.limit g
      (w.limit.sourceEndpoint (mergeVertex w) s₀) →
      g.1.1 ∈ GluingDatum.incidentEdges (mergeVertex w) := fun g hg ↦
    target_mem_incidentEdges _ hg
  have hWallInc' : ∀ g : w'.limit.SourceEdge, Incident w'.limit g
      (w'.limit.sourceEndpoint (mergeVertex w') (ψ.vertexPerm (mergeVertex w) s₀)) →
      g.1.1 ∈ GluingDatum.incidentEdges (mergeVertex w') := fun g hg ↦
    target_mem_incidentEdges _ hg
  have hst : ∀ g, g ∈ rSurv w u s₀ ↔
      ψ.sourceEdgeEquiv g ∈ rSurv w' u' (ψ.vertexPerm (mergeVertex w) s₀) := by
    intro g
    have hA : g ∈ rSurv w u s₀ ↔ (g ∈ ndAt w.limit (w.limit.sourceEndpoint (mergeVertex w) s₀) ∧
        unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
          g.1.1 ∈ GluingDatum.incidentEdges u) :=
      mem_sideSurv _ _ _ _ _ _ _
    have hB : ψ.sourceEdgeEquiv g ∈ rSurv w' u' (ψ.vertexPerm (mergeVertex w) s₀) ↔
        (ψ.sourceEdgeEquiv g ∈ ndAt w'.limit
          (w'.limit.sourceEndpoint (mergeVertex w') (ψ.vertexPerm (mergeVertex w) s₀)) ∧
        unfoldEdge rfl (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column)
          (ψ.sourceEdgeEquiv g).1.1 ∈ GluingDatum.incidentEdges u') :=
      mem_sideSurv _ _ _ _ _ _ _
    rw [hA, hB]
    have hnd : g ∈ ndAt w.limit (w.limit.sourceEndpoint (mergeVertex w) s₀) ↔
        ψ.sourceEdgeEquiv g ∈ ndAt w'.limit
          (w'.limit.sourceEndpoint (mergeVertex w') (ψ.vertexPerm (mergeVertex w) s₀)) := by
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := (mem_ndAt _ _ _).mp h
        refine (mem_ndAt _ _ _).mpr ⟨fun hd ↦ h1 ((ψ.isDangling_map_iff hConn g).mp hd), ?_⟩
        rw [← hV]
        exact (ψ.incident_map_iff g _).mpr h2
      · intro h
        obtain ⟨h1, h2⟩ := (mem_ndAt _ _ _).mp h
        rw [← hV] at h2
        exact (mem_ndAt _ _ _).mpr ⟨fun hd ↦ h1 ((ψ.isDangling_map_iff hConn g).mpr hd),
          (ψ.incident_map_iff g _).mp h2⟩
    rw [← hnd]
    refine and_congr_right fun hg ↦ ?_
    have hinc := hWallInc g ((mem_ndAt _ _ _).mp hg).2
    have hinc' : ψ.targetEdge g.1.1 ∈ GluingDatum.incidentEdges (mergeVertex w') :=
      (W3Nd2StarExhaustionProof.incident_iff ψ hWall g.1.1).mp
        (ValencyThreeResolutionMatch.ends_of_mem hinc)
    rw [← hside _ hinc]
    change _ ↔ unfoldEdge rfl (fst_ne_snd (w'.frame.edgeOf w'.column))
      (w'.frame.numEdges_edgeOf w'.column) (ψ.targetEdge g.1.1) ∈ GluingDatum.incidentEdges u'
    rw [← hside' _ hinc']
    exact ⟨fun h ↦ (hsec g.1.1).trans h, fun h ↦ (hsec g.1.1).symm.trans h⟩
  refine ⟨(Finset.card_equiv ψ.sourceEdgeEquiv hst).symm, ?_⟩
  unfold rSum sideSum
  exact (Finset.sum_equiv ψ.sourceEdgeEquiv hst fun g _ ↦ (ψ.sourceEdgeIndex_map g).symm).symm

/-- **Corresponding classes have the same size.** -/
theorem rCnt_true_map (w : Regrowth core y degree) (w' : Regrowth c₂ y degree)
    (ψ : GeometricDatumIso w.limit w'.limit)
    (hWall : ψ.targetVertex (mergeVertex w) = mergeVertex w') (s₀ : Fin degree) :
    rCnt w' (fun _ ↦ True) (ψ.vertexPerm (mergeVertex w) s₀) = rCnt w (fun _ ↦ True) s₀ := by
  unfold rCnt
  rw [cnt_eq_natCard, cnt_eq_natCard]
  refine Nat.card_congr ?_
  refine (Equiv.subtypeEquiv (ψ.vertexPerm (mergeVertex w)).symm fun u ↦ ?_)
  rw [← wall_rel_iff_merged, ← wall_rel_iff_merged]
  simp only [and_true]
  rw [← hWall, ← wall_rel_map ψ (mergeVertex w), Equiv.apply_symm_apply]

/-- **A class with two limit survivors on each side is the anchor class.**  Its limit vertex
has surviving valency at least four, hence exactly four, hence is the anchor. -/
theorem repr_eq_block_of_two (w : Regrowth core y degree) {block}
    (H : ValencyFourSplit.RegrowthAnchor4 w block) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y) {u v : w.frame.target.V}
    (huv : (u = endA w ∧ v = endB w) ∨ (u = endB w ∧ v = endA w)) (s₀ : Fin degree)
    (hu : 2 ≤ (rSurv w u s₀).card) (hv : 2 ≤ (rSurv w v s₀).card) :
    (mergedPartition w.frame.data (endA w) (endB w)).repr s₀ = block.1 := by
  classical
  set V := w.limit.sourceEndpoint (mergeVertex w) s₀ with hV
  have hsub : rSurv w u s₀ ∪ rSurv w v s₀ ⊆ ndAt w.limit V := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact ((mem_sideSurv _ _ _ _ _ _ _).mp hg).1
    · exact ((mem_sideSurv _ _ _ _ _ _ _).mp hg).1
  have hdisj : Disjoint (rSurv w u s₀) (rSurv w v s₀) := by
    rw [Finset.disjoint_left]
    intro g hgu hgv
    have h1 := ((mem_sideSurv _ _ _ _ _ _ _).mp hgu).2
    have h2 := ((mem_sideSurv _ _ _ _ _ _ _).mp hgv).2
    exact ValencyThreeSplit.not_mem_incidentEdges_other rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) huv h1 (unfoldEdge_ne_contracted _ _ _ _) h2
  have hge : 4 ≤ nonDanglingValency w.limit V := by
    rw [← card_ndAt]
    calc 4 ≤ (rSurv w u s₀).card + (rSurv w v s₀).card := by omega
      _ = (rSurv w u s₀ ∪ rSurv w v s₀).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hle : nonDanglingValency w.limit V ≤ 4 :=
    NonTrivalentUniqueFourValent.nonDanglingValency_le_four w.frame.data w.frame.fullDim
      rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) H.star
      H.compat V
  have hA := ValencyFourSplit.eq_anchorOf_of_nd4 w H e₀ hpt V (by omega)
  have h := congrArg (fun X : w.limit.SourceVertex ↦ X.1.2) hA
  change (w.limit.vertexPartition (mergeVertex w)).repr s₀ = block.1 at h
  rwa [limit_wall_partition] at h

/-- **Equal splits give equal bridge counts at the anchor class**: the `hK` input of the
transport, from `K`-rigidity along the limit isomorphism (`numbers_eq_of_limitIso`). -/
theorem hK_of_reads4 (w : Regrowth core y degree) (w' : Regrowth c₂ y degree) {block block'}
    (H : ValencyFourSplit.RegrowthAnchor4 w block) (H' : ValencyFourSplit.RegrowthAnchor4 w' block')
    (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (ψ : GeometricDatumIso w.limit w'.limit)
    (hWall : ψ.targetVertex (mergeVertex w) = mergeVertex w')
    (L : ValencyFourSplit.Labelling4 w.limit (anchorOf w block))
    (L' : ValencyFourSplit.Labelling4 w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) {s : ValencyFourSplit.Split4}
    (hs : ValencyFourSplit.Reads4 L s) (hs' : ValencyFourSplit.Reads4 L' s)
    {u v : w.frame.target.V} (huv : (u = endA w ∧ v = endB w) ∨ (u = endB w ∧ v = endA w))
    {u' v' : w'.frame.target.V}
    (huv' : (u' = endA w' ∧ v' = endB w') ∨ (u' = endB w' ∧ v' = endA w')) (s₀ : Fin degree)
    (hu : 2 ≤ (rSurv w u s₀).card) (hv : 2 ≤ (rSurv w v s₀).card) :
    rCnt w (fun s ↦ Act w.frame.data u s ∧ Act w.frame.data v s) s₀ =
      rCnt w' (fun s ↦ Act w'.frame.data u' s ∧ Act w'.frame.data v' s)
        (ψ.vertexPerm (mergeVertex w) s₀) := by
  classical
  have hr := repr_eq_block_of_two w H e₀ hpt huv s₀ hu hv
  -- the image class is the far anchor class
  have hr' : (mergedPartition w'.frame.data (endA w') (endB w')).repr
      (ψ.vertexPerm (mergeVertex w) s₀) = block'.1 := by
    have hV : ψ.sourceVertexEquiv (w.limit.sourceEndpoint (mergeVertex w) s₀) =
        w'.limit.sourceEndpoint (mergeVertex w') (ψ.vertexPerm (mergeVertex w) s₀) := by
      rw [sourceVertexEquiv_sourceEndpoint, hWall]
    have hA : w.limit.sourceEndpoint (mergeVertex w) s₀ = anchorOf w block := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (w.limit.vertexPartition (mergeVertex w)).repr s₀ = block.1
        rw [limit_wall_partition]
        exact hr
    have hA' := ValencyFourSplit.sourceVertexEquiv_anchorOf4 w w' H H' e₀ hpt ψ
    rw [← hA, hV] at hA'
    have h := congrArg (fun X : w'.limit.SourceVertex ↦ X.1.2) hA'
    change (w'.limit.vertexPartition (mergeVertex w')).repr _ = block'.1 at h
    rwa [limit_wall_partition] at h
  obtain ⟨P⟩ := ValencyFourSplit.shape w.frame.fullDim H
  obtain ⟨P'⟩ := ValencyFourSplit.shape w'.frame.fullDim H'
  have hboth : ∀ {c : Core n p} (x : Regrowth c y degree) {uu vv : x.frame.target.V},
      ((uu = endA x ∧ vv = endB x) ∨ (uu = endB x ∧ vv = endA x)) →
      ∀ t, rCnt x (fun s ↦ Act x.frame.data uu s ∧ Act x.frame.data vv s) t =
        rCnt x (fun s ↦ Act x.frame.data (endA x) s ∧ Act x.frame.data (endB x) s) t := by
    intro c x uu vv h t
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact cnt_and_comm x.frame.data _ _ t
  rw [hboth w huv, hboth w' huv']
  unfold rCnt
  rw [cnt_both_eq_index w.frame.data w.frame.fullDim rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) (H.changeZero w.frame.fullDim) P hr,
    cnt_both_eq_index w'.frame.data w'.frame.fullDim rfl (fst_ne_snd (w'.frame.edgeOf w'.column))
      (w'.frame.numEdges_edgeOf w'.column) (H'.changeZero w'.frame.fullDim) P' hr']
  exact (ValencyFourSplit.numbers_eq_of_limitIso w.frame.fullDim w'.frame.fullDim H H' P P' ψ
    (ValencyFourSplit.sourceVertexEquiv_anchorOf4 w w' H H' e₀ hpt ψ) L L' hL hs hs').1

end RegrowthCounts

/-! ## 14.  The transport between two regrowths at one valency-four metric limit -/

section MainTransport

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open W4WallExhaustion (mergeVertex)
open ValencyThreeRigidity (IsPlacement resolutionOf endA endB)
open ValencyThreeSplit (ndAt mem_ndAt card_ndAt target_mem_incidentEdges anchorOf)
open ResolutionExpansionFree (TransportFree)

variable {n p degree : ℕ} {core c₂ : Core n p} {y : Fin p → ℚ}

theorem sourceEdgeEquiv_sourceEdge {T₁ T₂ : CFGraph} {first : GluingDatum T₁ degree}
    {second : GluingDatum T₂ degree} (ψ : GeometricDatumIso first second) (e : T₁.edges)
    (s : Fin degree) :
    ψ.sourceEdgeEquiv (first.sourceEdge e s) =
      second.sourceEdge (ψ.targetEdge e) (ψ.edgePerm e s) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change ψ.edgePerm e ((first.edgePartition e).repr s) =
      (second.edgePartition (ψ.targetEdge e)).repr (ψ.edgePerm e s)
    rw [ψ.edgePartition e]
    change _ = ψ.edgePerm e ((first.edgePartition e).repr ((ψ.edgePerm e).symm
      (ψ.edgePerm e s)))
    rw [Equiv.symm_apply_apply]

/-- **One wall occurrence realigned onto the wall permutation `τ`.**  Given `τ` agreeing with
the wall permutation modulo the wall partition and matching the activity of the occurrence's
end, the limit isomorphism can be realigned (on the occurrence's pendant branch only) so that
the occurrence's permutation agrees with `τ` on its inactive sheets and carries its active
sheets to active ones. -/
theorem exists_realign_good (w : Regrowth core y degree) (w' : Regrowth c₂ y degree)
    {block block'} (H : ValencyFourSplit.RegrowthAnchor4 w block)
    (H' : ValencyFourSplit.RegrowthAnchor4 w' block')
    (ψ₀ : GeometricDatumIso w.limit w'.limit)
    (hWall₀ : ψ₀.targetVertex (mergeVertex w) = mergeVertex w')
    (τ : Equiv.Perm (Fin degree))
    (hτν : ∀ s, (w'.limit.vertexPartition (mergeVertex w')).Rel (τ s)
      (ψ₀.vertexPerm (mergeVertex w) s))
    {uu : w.frame.target.V} (huu : uu = endA w ∨ uu = endB w)
    {uu' : w'.frame.target.V}
    (hτact : ∀ s, Act w'.frame.data uu' (τ s) ↔ Act w.frame.data uu s)
    (t : (w.frame.limitTarget w.column).edges) (ht : t ∈ GluingDatum.incidentEdges (mergeVertex w))
    (htu : unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) t ∈
      GluingDatum.incidentEdges uu)
    (htu' : unfoldEdge rfl (fst_ne_snd (w'.frame.edgeOf w'.column))
      (w'.frame.numEdges_edgeOf w'.column) (ψ₀.targetEdge t) ∈ GluingDatum.incidentEdges uu') :
    ∃ ψ₁ : GeometricDatumIso w.limit w'.limit,
      (∀ e, ψ₁.targetEdge e = ψ₀.targetEdge e) ∧ (∀ v, ψ₁.targetVertex v = ψ₀.targetVertex v) ∧
      (∀ v, ψ₀.targetVertex v = mergeVertex w' → ψ₁.vertexPerm v = ψ₀.vertexPerm v) ∧
      (∀ e, ψ₀.targetEdge e ∈ GluingDatum.incidentEdges (mergeVertex w') →
        ψ₀.targetEdge e ≠ ψ₀.targetEdge t → ψ₁.edgePerm e = ψ₀.edgePerm e) ∧
      ∀ s, (¬ Act w.frame.data uu s → ψ₁.edgePerm t s = τ s) ∧
        (Act w.frame.data uu s → Act w'.frame.data uu' (ψ₁.edgePerm t s)) := by
  classical
  set W' := w'.limit.vertexPartition (mergeVertex w')
  set ν := ψ₀.vertexPerm (mergeVertex w)
  set σ := ψ₀.edgePerm t
  have hConn := ValencyThreeSplit.connected_limit w
  have hConn' := ValencyThreeSplit.connected_limit w'
  have htInc' : ψ₀.targetEdge t ∈ GluingDatum.incidentEdges (mergeVertex w') :=
    (W3Nd2StarExhaustionProof.incident_iff ψ₀ hWall₀ t).mp (ValencyThreeResolutionMatch.ends_of_mem ht)
  have hν : ∀ s u, W'.Rel (ν s) (ν u) ↔ (w.limit.vertexPartition (mergeVertex w)).Rel s u := by
    intro s u
    rw [← wall_rel_map ψ₀ (mergeVertex w) s u, hWall₀]
  have hσ : ∀ s, W'.Rel (σ s) (ν s) := by
    intro s
    have h := W3Nd2StarExhaustionProof.edgePerm_agree ψ₀ hWall₀ t htInc' s
    have h2 := (hν ((ψ₀.vertexPerm (mergeVertex w)).symm (σ s)) s).mpr h
    change W'.Rel (ν (ν.symm (σ s))) (ν s) at h2
    rwa [Equiv.apply_symm_apply] at h2
  set D' : Fin degree → Prop := fun x ↦
    0 < nonDanglingValency w'.limit (w'.limit.sourceEndpoint (mergeVertex w') x) ∧
      IsDangling w'.limit (w'.limit.sourceEdge (ψ₀.targetEdge t) x)
  have hSurv : ∀ s, ¬ D' (σ s) → Act w.frame.data uu s → Act w'.frame.data uu' (σ s) := by
    intro s hD hs
    have hpos := limit_active_of_act w.frame.data w.frame.fullDim rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) (H.changeZero w.frame.fullDim) H.compat huu hs
    have hpos' : 0 < nonDanglingValency w'.limit
        (w'.limit.sourceEndpoint (mergeVertex w') (σ s)) := by
      rw [GluingDatum.sourceEndpoint_congr _ _ (hσ s), ← hWall₀,
        ← sourceVertexEquiv_sourceEndpoint, ψ₀.nonDanglingValency_map hConn]
      exact hpos
    have hnd : ¬ IsDangling w'.limit (w'.limit.sourceEdge (ψ₀.targetEdge t) (σ s)) :=
      fun h ↦ hD ⟨hpos', h⟩
    exact act_of_survives w'.frame.data rfl (fst_ne_snd (w'.frame.edgeOf w'.column))
      (w'.frame.numEdges_edgeOf w'.column) H'.compat htu' hnd
  have hInact : ∀ s, ¬ D' (σ s) → ¬ Act w.frame.data uu s → σ s = τ s := by
    intro s hD hs
    have hdang : IsDangling w.limit (w.limit.sourceEdge t s) := by
      by_contra h
      exact hs (act_of_survives w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) H.compat htu h)
    have hdang' : IsDangling w'.limit (w'.limit.sourceEdge (ψ₀.targetEdge t) (σ s)) := by
      rw [← sourceEdgeEquiv_sourceEdge]
      exact (ψ₀.isDangling_map_iff hConn _).mpr hdang
    have h0 : nonDanglingValency w'.limit (w'.limit.sourceEndpoint (mergeVertex w') (σ s)) = 0 := by
      by_contra h
      exact hD ⟨Nat.pos_of_ne_zero h, hdang'⟩
    have hrel : W'.Rel (σ s) (τ s) := (hσ s).trans (hτν s).symm
    rw [wall_rel_iff_merged] at hrel
    exact (eq_of_limit_inactive w'.frame.data w'.frame.fullDim rfl
      (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column)
      (H'.changeZero w'.frame.fullDim) h0 H'.compat hrel).symm
  obtain ⟨ρ, hρσ, hρν, hρτ, hρact⟩ := exists_rho W' ν σ τ hσ hτν (Act w.frame.data uu)
    (Act w'.frame.data uu') D' hτact hSurv hInact
  have hNoGlue' : DanglingEdgeNoGlue w'.limit :=
    danglingEdgeNoGlue_contractDatum w'.frame.data H'.compat.2 w'.frame.fullDim.danglingEdgeNoGlue
  obtain ⟨ψ₁, h₁, h₂, h₃, h₄, h₅⟩ := exists_realign w' H'.forest hNoGlue' ψ₀ t htInc' ρ
    (fun s hs ↦ hρσ s hs) (fun s _ ↦ (hρν s).trans (hσ s).symm)
  refine ⟨ψ₁, h₁, h₂, h₃, h₄, fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩⟩
  · rw [h₅]; exact hρτ s hs
  · rw [h₅]; exact hρact s hs

/-- **The transport of the two incoming resolutions**, after realigning the limit isomorphism
on the four wall occurrences.  Inputs: the two anchor inputs, a limit isomorphism carrying wall
to wall, two placements matched along it with their shapes, and (the only valency-four input)
equal bridge indices at the anchor class. -/
theorem exists_transport (w : Regrowth core y degree) (w' : Regrowth c₂ y degree) {block block'}
    (H : ValencyFourSplit.RegrowthAnchor4 w block) (H' : ValencyFourSplit.RegrowthAnchor4 w' block')
    (ψ : GeometricDatumIso w.limit w'.limit)
    (hWall : ψ.targetVertex (mergeVertex w) = mergeVertex w')
    {u v : w.frame.target.V} (huv : (u = endA w ∧ v = endB w) ∨ (u = endB w ∧ v = endA w))
    {u' v' : w'.frame.target.V}
    (huv' : (u' = endA w' ∧ v' = endB w') ∨ (u' = endB w' ∧ v' = endA w'))
    (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second)
    (second' : (w'.frame.limitTarget w'.column).edges → Bool) (h' : IsPlacement w' second')
    (hS : ResShape (w.limit.vertexPartition (mergeVertex w)) (resolutionOf w second h)
      (Act w.frame.data u) (Act w.frame.data v))
    (hS' : ResShape (w'.limit.vertexPartition (mergeVertex w')) (resolutionOf w' second' h')
      (Act w'.frame.data u') (Act w'.frame.data v'))
    (hsideU : ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), second e = false ↔
      unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) e ∈
        GluingDatum.incidentEdges u)
    (hsideV : ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), second e = true ↔
      unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) e ∈
        GluingDatum.incidentEdges v)
    (hsideU' : ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w'), second' e = false ↔
      unfoldEdge rfl (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column) e ∈
        GluingDatum.incidentEdges u')
    (hsideV' : ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w'), second' e = true ↔
      unfoldEdge rfl (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column) e ∈
        GluingDatum.incidentEdges v')
    (hsec : ∀ e, second' (ψ.targetEdge e) = second e)
    (hK : ∀ s₀, 2 ≤ (rSurv w u s₀).card → 2 ≤ (rSurv w v s₀).card →
      rCnt w (fun s ↦ Act w.frame.data u s ∧ Act w.frame.data v s) s₀ =
        rCnt w' (fun s ↦ Act w'.frame.data u' s ∧ Act w'.frame.data v' s)
          (ψ.vertexPerm (mergeVertex w) s₀)) :
    ∃ ψ₄ : GeometricDatumIso w.limit w'.limit, (∀ e, ψ₄.targetEdge e = ψ.targetEdge e) ∧
      Nonempty (TransportFree ψ₄ (mergeVertex w) (mergeVertex w') second second'
        (resolutionOf w second h) (resolutionOf w' second' h')) := by
  classical
  set D := w.frame.data
  set D' := w'.frame.data
  set W := w.limit.vertexPartition (mergeVertex w)
  set W' := w'.limit.vertexPartition (mergeVertex w')
  set ν := ψ.vertexPerm (mergeVertex w)
  have hConn := ValencyThreeSplit.connected_limit w
  have hCZ := H.changeZero w.frame.fullDim
  have hCZ' := H'.changeZero w'.frame.fullDim
  have hν : ∀ s t, W'.Rel (ν s) (ν t) ↔ W.Rel s t := by
    intro s t
    rw [← wall_rel_map ψ (mergeVertex w) s t, hWall]
  have huv0 : (u = endA w ∧ v = endB w) ∨ (u = endB w ∧ v = endA w) := huv
  have hu : u = endA w ∨ u = endB w := by rcases huv with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have hv : v = endA w ∨ v = endB w := by rcases huv with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  have hu' : u' = endA w' ∨ u' = endB w' := by rcases huv' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have hv' : v' = endA w' ∨ v' = endB w' := by rcases huv' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  -- the class counts correspond
  have hcounts : ∀ s₀, rCnt w (Act D u) s₀ = rCnt w' (Act D' u') (ν s₀) ∧
      rCnt w (Act D v) s₀ = rCnt w' (Act D' v') (ν s₀) ∧
      rCnt w (fun s ↦ Act D u s ∧ Act D v s) s₀ =
        rCnt w' (fun s ↦ Act D' u' s ∧ Act D' v' s) (ν s₀) := by
    intro s₀
    have hF := classFactsUV D w.frame.fullDim rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) hCZ H.compat huv s₀
    have hF' := classFactsUV D' w'.frame.fullDim rfl (fst_ne_snd (w'.frame.edgeOf w'.column))
      (w'.frame.numEdges_edgeOf w'.column) hCZ' H'.compat huv' (ν s₀)
    obtain ⟨hNu, hSu⟩ := rSurv_map w w' ψ hWall second second' hsec false u u' hsideU hsideU' s₀
    obtain ⟨hNv, hSv⟩ := rSurv_map w w' ψ hWall second second' hsec true v v' hsideV hsideV' s₀
    have hn := rCnt_true_map w w' ψ hWall s₀
    change ClassFacts (rCnt w' (Act D' u') (ν s₀)) (rCnt w' (Act D' v') (ν s₀))
      (rCnt w' (fun s ↦ Act D' u' s ∧ Act D' v' s) (ν s₀)) (rCnt w' (fun _ ↦ True) (ν s₀))
      (rSurv w' u' (ν s₀)).card (rSum w' u' (ν s₀)) (rSurv w' v' (ν s₀)).card
      (rSum w' v' (ν s₀)) at hF'
    rw [hNu, hSu, hNv, hSv, hn] at hF'
    have := ClassFacts.eq hF hF' (hK s₀)
    exact ⟨this.1, this.2.1, this.2.2⟩
  -- the wall permutation `τ`
  have toCard : ∀ (P : Fin degree → Prop) [DecidablePred P] (s₀ : Fin degree),
      Nat.card {s // W.Rel s₀ s ∧ P s} = rCnt w P s₀ := by
    intro P _ s₀
    unfold rCnt
    rw [cnt_eq_natCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun s ↦ by rw [wall_rel_iff_merged])
  have toCard' : ∀ (P : Fin degree → Prop) [DecidablePred P] (s₀ : Fin degree),
      Nat.card {s // W'.Rel s₀ s ∧ P s} = rCnt w' P s₀ := by
    intro P _ s₀
    unfold rCnt
    rw [cnt_eq_natCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun s ↦ by rw [wall_rel_iff_merged])
  obtain ⟨τ, hτ⟩ := exists_tau W W' ν hν (Act D u) (Act D v) (Act D' u') (Act D' v')
    (fun s₀ ↦ by
      have h1 := toCard (fun _ ↦ True) s₀
      have h2 := toCard' (fun _ ↦ True) (ν s₀)
      have h3 := rCnt_true_map w w' ψ hWall s₀
      have e1 : {s // W.Rel s₀ s} ≃ {s // W.Rel s₀ s ∧ True} :=
        Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨h, trivial⟩, And.left⟩
      have e2 : {s // W'.Rel (ν s₀) s} ≃ {s // W'.Rel (ν s₀) s ∧ True} :=
        Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨h, trivial⟩, And.left⟩
      rw [Nat.card_congr e1, Nat.card_congr e2, h1, h2, h3])
    (fun s₀ ↦ by rw [toCard, toCard', (hcounts s₀).1])
    (fun s₀ ↦ by rw [toCard, toCard', (hcounts s₀).2.1])
    (fun s₀ ↦ by rw [toCard, toCard', (hcounts s₀).2.2])
  -- realign every wall occurrence onto `τ`
  let Good : GeometricDatumIso w.limit w'.limit → (w.frame.limitTarget w.column).edges → Prop :=
    fun φ e ↦ (second e = false → ∀ s, (¬ Act D u s → φ.edgePerm e s = τ s) ∧
        (Act D u s → Act D' u' (φ.edgePerm e s))) ∧
      (second e = true → ∀ s, (¬ Act D v s → φ.edgePerm e s = τ s) ∧
        (Act D v s → Act D' v' (φ.edgePerm e s)))
  have hStep : ∀ S : Finset (w.frame.limitTarget w.column).edges,
      S ⊆ GluingDatum.incidentEdges (mergeVertex w) →
      ∃ φ : GeometricDatumIso w.limit w'.limit, (∀ e, φ.targetEdge e = ψ.targetEdge e) ∧
        (∀ v, φ.targetVertex v = ψ.targetVertex v) ∧ φ.vertexPerm (mergeVertex w) = ν ∧
        ∀ e ∈ S, Good φ e := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨ψ, fun _ ↦ rfl, fun _ ↦ rfl, rfl, fun e he ↦ absurd he (by simp)⟩
    | insert t S htS ih =>
      intro hsub
      obtain ⟨φ, hφE, hφV, hφν, hφG⟩ := ih (fun x hx ↦ hsub (Finset.mem_insert_of_mem hx))
      have ht : t ∈ GluingDatum.incidentEdges (mergeVertex w) := hsub (Finset.mem_insert_self _ _)
      have hWφ : φ.targetVertex (mergeVertex w) = mergeVertex w' := (hφV _).trans hWall
      have hτν : ∀ s, W'.Rel (τ s) (φ.vertexPerm (mergeVertex w) s) := fun s ↦ by
        rw [hφν]; exact (hτ s).1
      have htInc' : ψ.targetEdge t ∈ GluingDatum.incidentEdges (mergeVertex w') :=
        (W3Nd2StarExhaustionProof.incident_iff ψ hWall t).mp (ValencyThreeResolutionMatch.ends_of_mem ht)
      have hkeep : ∀ (φ₁ : GeometricDatumIso w.limit w'.limit),
          (∀ e, φ₁.targetEdge e = φ.targetEdge e) →
          (∀ e, φ.targetEdge e ∈ GluingDatum.incidentEdges (mergeVertex w') →
            φ.targetEdge e ≠ φ.targetEdge t → φ₁.edgePerm e = φ.edgePerm e) →
          ∀ e ∈ S, Good φ₁ e := by
        intro φ₁ _ h₄ e he
        have heInc : e ∈ GluingDatum.incidentEdges (mergeVertex w) :=
          hsub (Finset.mem_insert_of_mem he)
        have heInc' : φ.targetEdge e ∈ GluingDatum.incidentEdges (mergeVertex w') :=
          (W3Nd2StarExhaustionProof.incident_iff φ hWφ e).mp
            (ValencyThreeResolutionMatch.ends_of_mem heInc)
        have hne : φ.targetEdge e ≠ φ.targetEdge t := fun h ↦ htS (φ.targetEdge.injective h ▸ he)
        have := h₄ e heInc' hne
        have hG := hφG e he
        simp only [Good, this]
        exact hG
      cases hb : second t with
      | false =>
        obtain ⟨φ₁, h₁, h₂, h₃, h₄, h₅⟩ := exists_realign_good w w' H H' φ hWφ τ hτν hu
          (fun s ↦ (hτ s).2.1) t ht ((hsideU t ht).mp hb)
          (by rw [hφE]; exact (hsideU' _ htInc').mp ((hsec t).trans hb))
        refine ⟨φ₁, fun e ↦ (h₁ e).trans (hφE e), fun v ↦ (h₂ v).trans (hφV v),
          (h₃ _ hWφ).trans hφν, fun e he ↦ ?_⟩
        rcases Finset.mem_insert.mp he with rfl | he
        · exact ⟨fun _ ↦ h₅, fun h ↦ absurd (hb.symm.trans h) (by simp)⟩
        · exact hkeep φ₁ h₁ h₄ e he
      | true =>
        obtain ⟨φ₁, h₁, h₂, h₃, h₄, h₅⟩ := exists_realign_good w w' H H' φ hWφ τ hτν hv
          (fun s ↦ (hτ s).2.2) t ht ((hsideV t ht).mp hb)
          (by rw [hφE]; exact (hsideV' _ htInc').mp ((hsec t).trans hb))
        refine ⟨φ₁, fun e ↦ (h₁ e).trans (hφE e), fun v ↦ (h₂ v).trans (hφV v),
          (h₃ _ hWφ).trans hφν, fun e he ↦ ?_⟩
        rcases Finset.mem_insert.mp he with rfl | he
        · exact ⟨fun h ↦ absurd (hb.symm.trans h) (by simp), fun _ ↦ h₅⟩
        · exact hkeep φ₁ h₁ h₄ e he
  obtain ⟨ψ₄, hE, hV, hν₄, hG⟩ := hStep _ subset_rfl
  have hWall₄ : ψ₄.targetVertex (mergeVertex w) = mergeVertex w' := (hV _).trans hWall
  have hmem : ∀ e : (w.frame.limitTarget w.column).edges,
      ((e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 = mergeVertex w ∨
        (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
          mergeVertex w) →
      e ∈ GluingDatum.incidentEdges (mergeVertex w) := fun e he ↦ by
    simpa [GluingDatum.incidentEdges] using he
  refine ⟨ψ₄, hE, transportFree_of_shape ψ₄ hWall₄ second second'
    (fun e ↦ by rw [hE]; exact hsec e) _ _ (Act D u) (Act D v) (Act D' u') (Act D' v') hS hS' τ
    (fun s ↦ ?_) (fun s ↦ (hτ s).2.1) (fun s ↦ (hτ s).2.2)
    (fun e he hb s ↦ (hG e (hmem e he)).1 hb s) (fun e he hb s ↦ (hG e (hmem e he)).2 hb s)⟩
  rw [hν₄]
  have h := (hτ s).1
  rw [← Equiv.apply_symm_apply ν (τ s), hν] at h
  exact h

end MainTransport

/-! ## 15.  Stages 4--5 at valency four: equal splits give one class -/

section SideMatch

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open W4WallExhaustion (mergeVertex)
open ValencyThreeRigidity (IsPlacement resolutionOf endA endB isPlacement_right
  extendsMetric_of_transportFree columnIso_of_extendsMetric frameIso_of_columns)
open ValencyThreeSplit (anchorOf fib)
open ValencyFourSplit (Labelling4 Split4 Reads4 labelsAt)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)

variable {n p degree : ℕ} {core c₂ : Core n p} {y : Fin p → ℚ}

/-- The incoming side assignment of a regrowth: `true` on the limit occurrences whose
unfolding meets the second end. -/
noncomputable abbrev rightW (w : Regrowth core y degree) :
    (w.frame.limitTarget w.column).edges → Bool :=
  IncomingTargetExpansion.right rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column)

theorem rightW_true_iff (w : Regrowth core y degree) (e : (w.frame.limitTarget w.column).edges) :
    rightW w e = true ↔ unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) e ∈ GluingDatum.incidentEdges (endB w) := by
  rw [mem_incidentEdges_iff]
  simp only [rightW, IncomingTargetExpansion.right, decide_eq_true_eq]

theorem rightW_false_iff (w : Regrowth core y degree) {e : (w.frame.limitTarget w.column).edges}
    (he : e ∈ GluingDatum.incidentEdges (mergeVertex w)) :
    rightW w e = false ↔ unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) e ∈ GluingDatum.incidentEdges (endA w) := by
  have h2 := ValencyThreeResolutionMatch.unfold_mem_ends (hc := rfl)
    (hOne := w.frame.numEdges_edgeOf w.column) he
  constructor
  · intro hf
    rcases h2 with h | h
    · exact h
    · have := (rightW_true_iff w e).mpr h
      rw [hf] at this
      exact absurd this (by decide)
  · intro ha
    by_contra ht
    have ht' : rightW w e = true := by simpa using ht
    exact ValencyThreeSplit.not_mem_incidentEdges_other rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) (Or.inl ⟨rfl, rfl⟩) ha (unfoldEdge_ne_contracted _ _ _ _)
      ((rightW_true_iff w e).mp ht')

/-- **The incoming side of a label is read off the split**: label `i` lies on the side of
label `0` exactly when it is `0` or the partner. -/
theorem right_label_iff (w : Regrowth core y degree) {block}
    (H : ValencyFourSplit.RegrowthAnchor4 w block) (L : Labelling4 w.limit (anchorOf w block))
    {s : Split4} (hs : Reads4 L s) (i : Fin 4) :
    rightW w (L.e i).1.1 = rightW w (L.e 0).1.1 ↔ (i = 0 ∨ i = s.partner) := by
  classical
  obtain ⟨hp0, X, hX, Y, hY, hXY, h0, hp, -⟩ := hs
  obtain ⟨P⟩ := ValencyFourSplit.shape w.frame.fullDim H
  obtain ⟨j, hj0, hXeq, -⟩ := ValencyFourSplit.labels_at w.frame.fullDim H P hX h0
  have hpj : s.partner = j := by
    rw [hXeq] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h
    · exact absurd h hp0
    · exact h
  have hLX : ∀ k, k ∈ labelsAt L X ↔ (k = 0 ∨ k = s.partner) := by
    intro k
    rw [hXeq, hpj]
    simp
  have hside := label_side L H P hX
  have hmem : ∀ k, (L.e k).1.1 ∈ GluingDatum.incidentEdges (mergeVertex w) := fun k ↦
    label_mem L k
  rw [← hLX, hside]
  rcases ValencyFourSplit.over_of_mem_fib hX with hXa | hXb
  · have h0' : rightW w (L.e 0).1.1 = false := by
      rw [rightW_false_iff w (hmem 0)]
      have := (hside 0).mp h0
      rwa [hXa] at this
    rw [h0', rightW_false_iff w (hmem i), hXa]
  · have h0' : rightW w (L.e 0).1.1 = true := by
      rw [rightW_true_iff w]
      have := (hside 0).mp h0
      rwa [hXb] at this
    rw [h0', rightW_true_iff w, hXb]

theorem bool_align {a a' b b' : Bool} (h : a' = b' ↔ a = b) :
    (b' = b → a' = a) ∧ (b' = !b → a' = !a) := by
  revert h
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

/-- **Stages 4--5 at valency four, for every class**: two anchored regrowths of one connected
core with at least three vertices, at a facet point, reading the same split (partner and `K`)
for labellings transported along a labelled-metric isomorphism of their limits, are one
class. -/
theorem frameClass_eq_of_reads4 (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (w w' : Regrowth core y degree) {block block'}
    (H : ValencyFourSplit.RegrowthAnchor4 w block) (H' : ValencyFourSplit.RegrowthAnchor4 w' block')
    (ψ : GeometricDatumIso w.limit w'.limit) (hψ : ValencyThreeSplit.IsMetricIso w w' ψ)
    (L : Labelling4 w.limit (anchorOf w block)) (L' : Labelling4 w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) {s : Split4}
    (hs : Reads4 L s) (hs' : Reads4 L' s) :
    FrameClass.mk w.frame = FrameClass.mk w'.frame := by
  classical
  have hWall : ψ.targetVertex (mergeVertex w) = mergeVertex w' :=
    congrArg (fun X : w'.limit.SourceVertex ↦ X.1.1)
      (ValencyFourSplit.sourceVertexEquiv_anchorOf4 w w' H H' e₀ hpt ψ)
  set second := rightW w with hsecond
  have h : IsPlacement w second := isPlacement_right w
  have hS := (resShape w H second h).1 (fun _ _ ↦ rfl)
  set second' : (w'.frame.limitTarget w'.column).edges → Bool :=
    fun e' ↦ second (ψ.targetEdge.symm e') with hsecond'
  have hsec : ∀ e, second' (ψ.targetEdge e) = second e := fun e ↦ by
    simp only [hsecond', Equiv.symm_apply_apply]
  have hLt : ∀ i, (L'.e i).1.1 = ψ.targetEdge (L.e i).1.1 := fun i ↦ by rw [hL i]; rfl
  have hlab' : ∀ e' ∈ GluingDatum.incidentEdges (mergeVertex w'), ∃ i, (L'.e i).1.1 = e' :=
    fun e' he' ↦ exists_label w'.frame.fullDim L' H' he'
  have hkey : ∀ i, (rightW w' (L'.e i).1.1 = rightW w' (L'.e 0).1.1 ↔
      second (L.e i).1.1 = second (L.e 0).1.1) := fun i ↦ by
    rw [right_label_iff w' H' L' hs' i, hsecond, right_label_iff w H L hs i]
  have hsideU : ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), second e = false ↔
      unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) e ∈
        GluingDatum.incidentEdges (endA w) := fun e he ↦ rightW_false_iff w he
  have hsideV : ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), second e = true ↔
      unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) e ∈
        GluingDatum.incidentEdges (endB w) := fun e _ ↦ rightW_true_iff w e
  have finish : ∀ (second' : (w'.frame.limitTarget w'.column).edges → Bool)
      (h' : IsPlacement w' second') (ψ₄ : GeometricDatumIso w.limit w'.limit),
      (∀ e, ψ₄.targetEdge e = ψ.targetEdge e) →
      Nonempty (ResolutionExpansionFree.TransportFree ψ₄ (mergeVertex w) (mergeVertex w') second
        second' (resolutionOf w second h) (resolutionOf w' second' h')) →
      FrameClass.mk w.frame = FrameClass.mk w'.frame := by
    intro second' h' ψ₄ hE ⟨T⟩
    have hψ₄ : ValencyThreeSplit.IsMetricIso w w' ψ₄ := fun e ↦ by rw [hE e]; exact hψ e
    obtain ⟨Φ, hcol⟩ := columnIso_of_extendsMetric
      (extendsMetric_of_transportFree w w' second h second' h' ψ₄ hψ₄ T)
    exact FrameClass.mk_eq_mk_iff.mpr ⟨frameIso_of_columns w w'.frame hconn hn hpt.1 Φ hcol⟩
  by_cases hb : rightW w' (L'.e 0).1.1 = second (L.e 0).1.1
  · -- the far placement agrees with the far incoming sides
    have hag : ∀ e' ∈ GluingDatum.incidentEdges (mergeVertex w'), rightW w' e' = second' e' := by
      intro e' he'
      obtain ⟨i, rfl⟩ := hlab' e' he'
      rw [hLt i, hsec, ← hLt i]
      exact (bool_align (hkey i)).1 hb
    have h' : IsPlacement w' second' := Or.inl hag
    have hS' := (resShape w' H' second' h').1 hag
    obtain ⟨ψ₄, hE, hT⟩ := exists_transport w w' H H' ψ hWall (Or.inl ⟨rfl, rfl⟩)
      (Or.inl ⟨rfl, rfl⟩) second h second' h' hS hS' hsideU hsideV
      (fun e' he' ↦ by rw [← hag e' he']; exact rightW_false_iff w' he')
      (fun e' he' ↦ by rw [← hag e' he']; exact rightW_true_iff w' e') hsec
      (fun s₀ ↦ hK_of_reads4 w w' H H' e₀ hpt ψ hWall L L' hL hs hs' (Or.inl ⟨rfl, rfl⟩)
        (Or.inl ⟨rfl, rfl⟩) s₀)
    exact finish second' h' ψ₄ hE hT
  · -- the far placement is the far incoming sides exchanged
    have hb' : rightW w' (L'.e 0).1.1 = !second (L.e 0).1.1 := by
      revert hb
      cases rightW w' (L'.e 0).1.1 <;> cases second (L.e 0).1.1 <;> decide
    have hdis : ∀ e' ∈ GluingDatum.incidentEdges (mergeVertex w'),
        rightW w' e' = !second' e' := by
      intro e' he'
      obtain ⟨i, rfl⟩ := hlab' e' he'
      rw [hLt i, hsec, ← hLt i]
      exact (bool_align (hkey i)).2 hb'
    have h' : IsPlacement w' second' := Or.inr hdis
    have hnag : ¬ Agrees w' second' := by
      intro hag
      have h1 : rightW w' (L'.e 0).1.1 = second' (L'.e 0).1.1 := hag _ (label_mem L' 0)
      rw [hdis _ (label_mem L' 0)] at h1
      revert h1
      cases second' (L'.e 0).1.1 <;> decide
    have hS' := (resShape w' H' second' h').2 hnag
    have hflip : ∀ e' ∈ GluingDatum.incidentEdges (mergeVertex w'),
        second' e' = !rightW w' e' := fun e' he' ↦ by rw [hdis e' he', Bool.not_not]
    obtain ⟨ψ₄, hE, hT⟩ := exists_transport w w' H H' ψ hWall (Or.inl ⟨rfl, rfl⟩)
      (Or.inr ⟨rfl, rfl⟩) second h second' h' hS hS' hsideU hsideV
      (fun e' he' ↦ by
        rw [hflip e' he', Bool.not_eq_false', rightW_true_iff w' e'])
      (fun e' he' ↦ by
        rw [hflip e' he', Bool.not_eq_true', rightW_false_iff w' he'])
      hsec
      (fun s₀ ↦ hK_of_reads4 w w' H H' e₀ hpt ψ hWall L L' hL hs hs' (Or.inl ⟨rfl, rfl⟩)
        (Or.inr ⟨rfl, rfl⟩) s₀)
    exact finish second' h' ψ₄ hE hT

end SideMatch

/-! ## 16.  Stage 3 at valency four: the partner is read on the core -/

section CoreReading4

open ValencyThreeSplit (ndAt mem_ndAt fib intl limA)
open ValencyThreeCoreSlots (AnchorFrame NoParallel CoreShare eq_of_noParallel vertexOf
  coreIncidence_vertexOf vertexOf_end e₁_survives eq_e₁_of_stablePath)
open ValencyFourSplit (Bridge Labelling4 lift4 labelsAt mem_labelsAt)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {core : Core n p}
variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

/-- **A valency-four bridge is an anchor frame** (`ValencyThreeCoreSlots.AnchorFrame`) with no
divalent
constituent. -/
def frameOfBridge (P : Bridge data hc hab hOne block) : AnchorFrame data hc hab hOne block where
  R := (data.sourceEnds P.e₁).1
  Y := (data.sourceEnds P.e₁).2
  e₁ := P.e₁
  R_mem := P.fst_mem
  Y_mem := P.snd_mem
  R_ne_Y := P.ends_ne
  R_nd := P.nd_fst
  Y_nd := P.nd_snd
  e₁_mem := P.e₁_mem
  e₁_R := P.e₁_mem_ndAt P.fst_mem
  e₁_Y := P.e₁_mem_ndAt P.snd_mem
  three X hX _ := (P.mem_fib_iff' X).mp hX
  two X hX h2 := absurd h2 (by rw [P.nd_eq_three hX]; norm_num)
  two_unique X hX _ _ h2 _ := absurd h2 (by rw [P.nd_eq_three hX]; norm_num)

variable (L : Labelling4 (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- **Two labels at one branch vertex.**

It is equivalent to the core reading `CoreShare` at a core with no slot parallel to `e₀`
(`paired4_iff_coreShare`), and, for label `0`, to "`0` or the partner" (`paired4_zero_iff`),
which is inhabited and strict (`0` is not paired with the two labels at the other branch
vertex). -/
def Paired4 (i j : Fin 4) : Prop :=
  ∃ Z ∈ fib data hc hab hOne block, i ∈ labelsAt L Z ∧ j ∈ labelsAt L Z

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem lift4_survives (hCompat : DanglingCompatible data hc hab hOne) (i : Fin 4) :
    ¬ IsDangling data (lift4 L i) := by
  obtain ⟨X, -, hi⟩ := ValencyFourSplit.exists_mem_labelsAt L hCompat i
  exact ((mem_ndAt data X _).mp ((mem_labelsAt L X i).mp hi)).1

/-- The incoming stable path of the label `i`. -/
noncomputable def pathOf4 (hCompat : DanglingCompatible data hc hab hOne) (i : Fin 4) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨lift4 L i, lift4_survives L hCompat i⟩

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem incidence_pos_of_label (hCompat : DanglingCompatible data hc hab hOne) {i : Fin 4}
    {Z : data.SourceVertex} (hi : i ∈ labelsAt L Z) :
    0 < StablePathCount.incidenceCount data Z (pathOf4 L hCompat i) := by
  rw [StablePathCount.incidenceCount_pos_iff]
  exact ⟨⟨lift4 L i, lift4_survives L hCompat i⟩,
    ((mem_ndAt data Z _).mp ((mem_labelsAt L Z i).mp hi)).2, rfl⟩

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem pathOf4_ne (hCompat : DanglingCompatible data hc hab hOne)
    (P : Bridge data hc hab hOne block) (i : Fin 4) :
    pathOf4 L hCompat i ≠ NonDanglingEdge.stablePath ⟨P.e₁, P.e₁_survives⟩ := by
  intro h
  have := eq_e₁_of_stablePath (frameOfBridge P) ⟨lift4 L i, lift4_survives L hCompat i⟩ h
  exact ValencyFourSplit.lift4_ne L i (by
    rw [show lift4 L i = P.e₁ from this]
    exact P.e₁_target)

variable (ident : Count.CoreIdentification core data) {e₀ : Fin p}

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- **The pairing of the four labels is read on the core** when no core slot is parallel to
`e₀`: two labels sit at one branch vertex exactly when their core slots meet at one end of
`e₀`.  (`→` holds without `NoParallel`.) -/
theorem paired4_iff_coreShare (hCompat : DanglingCompatible data hc hab hOne)
    (P : Bridge data hc hab hOne block)
    (he₁ : ident.row (NonDanglingEdge.stablePath ⟨P.e₁, P.e₁_survives⟩) = e₀)
    (hpar : NoParallel core e₀) (i j : Fin 4) :
    Paired4 L i j ↔ CoreShare core e₀ (ident.row (pathOf4 L hCompat i))
      (ident.row (pathOf4 L hCompat j)) := by
  set Fr := frameOfBridge P
  have hRY : ∀ Z ∈ fib data hc hab hOne block, Z = Fr.R ∨ Z = Fr.Y := fun Z hZ ↦
    (P.mem_fib_iff' Z).mp hZ
  have hslot : ∀ k, ident.row (pathOf4 L hCompat k) ≠ e₀ := fun k h ↦
    pathOf4_ne L hCompat P k (ident.row.injective (h.trans he₁.symm))
  constructor
  · rintro ⟨Z, hZ, hi, hj⟩
    have h3 := P.nd_eq_three hZ
    refine ⟨vertexOf ident Z h3, vertexOf_end Fr ident he₁ Z (hRY Z hZ) h3, ?_, ?_⟩
    · rw [coreIncidence_vertexOf]; exact incidence_pos_of_label L hCompat hi
    · rw [coreIncidence_vertexOf]; exact incidence_pos_of_label L hCompat hj
  · rintro ⟨x, hx, hxi, hxj⟩
    obtain ⟨Zi, hZi, hi⟩ := ValencyFourSplit.exists_mem_labelsAt L hCompat i
    obtain ⟨Zj, hZj, hj⟩ := ValencyFourSplit.exists_mem_labelsAt L hCompat j
    have hi3 := P.nd_eq_three hZi
    have hj3 := P.nd_eq_three hZj
    have hvi : vertexOf ident Zi hi3 = x := by
      refine eq_of_noParallel hpar (hslot i) (vertexOf_end Fr ident he₁ Zi (hRY Zi hZi) hi3) hx
        ?_ hxi
      rw [coreIncidence_vertexOf]; exact incidence_pos_of_label L hCompat hi
    have hvj : vertexOf ident Zj hj3 = x := by
      refine eq_of_noParallel hpar (hslot j) (vertexOf_end Fr ident he₁ Zj (hRY Zj hZj) hj3) hx
        ?_ hxj
      rw [coreIncidence_vertexOf]; exact incidence_pos_of_label L hCompat hj
    have hZ : Zi = Zj := congrArg Subtype.val (ident.vertex.injective (hvi.trans hvj.symm))
    subst hZ
    exact ⟨Zi, hZi, hi, hj⟩

/-- **The partner is the label paired with `0`.** -/
theorem paired4_zero_iff (fd : FullDimensionalSourcePresentation data coordinate)
    (H : ValencyFourSplit.AnchorInput4 data hc hab hOne block) {s : ValencyFourSplit.Split4}
    (hs : ValencyFourSplit.Reads4 L s) (j : Fin 4) :
    Paired4 L 0 j ↔ (j = 0 ∨ j = s.partner) := by
  classical
  obtain ⟨hp0, X, hX, Y, hY, hXY, h0, hp, -⟩ := hs
  obtain ⟨P⟩ := ValencyFourSplit.shape fd H
  obtain ⟨k, hk0, hXeq, -⟩ := ValencyFourSplit.labels_at fd H P hX h0
  have hpk : s.partner = k := by
    rw [hXeq] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h
    · exact absurd h hp0
    · exact h
  constructor
  · rintro ⟨Z, hZ, hZ0, hZj⟩
    have hZX := ValencyFourSplit.eq_of_mem_labelsAt L hZ hX hZ0 h0
    subst hZX
    rw [hXeq] at hZj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZj
    rcases hZj with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hpk.symm)
  · rintro (rfl | rfl)
    · exact ⟨X, hX, h0, h0⟩
    · exact ⟨X, hX, h0, hp⟩

end CoreReading4

/-! ## 17.  Stage 3 on regrowths, and `K`-injectivity at a core with no parallel slot -/

section Injectivity

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyThreeSplit (anchorOf mem_ndAt IsMetricIso)
open ValencyThreeCoreSlots (WallRows inRow row_inRow_map NoParallel CoreShare row_e₁)
open ValencyFourSplit (Labelling4 Split4 Reads4 RegrowthAnchor4 V4Limit kIndexL kIndexR
  kIndexL_spec kIndexR_spec)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The contraction forest and no contracted return, at a valency-four anchor. -/
theorem wallRows4 {w : Regrowth core y degree} {block} (H : RegrowthAnchor4 w block) :
    WallRows w :=
  ⟨H.forest, StablePathFacetContraction.noContractedReturn_of_fourStar w.frame.data
    w.frame.fullDim rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    H.star⟩

/-- The incoming path of a label is the incoming row of its limit stable path. -/
theorem pathOf4_eq_inRow {w : Regrowth core y degree} {block} (H : RegrowthAnchor4 w block)
    (L : Labelling4 w.limit (anchorOf w block)) (i : Fin 4) :
    pathOf4 L H.compat i = inRow (wallRows4 H) (NonDanglingEdge.stablePath
      (⟨L.e i, ((mem_ndAt _ _ _).mp (L.mem i)).1⟩ : NonDanglingEdge w.limit)) :=
  rfl

/-- **A labelled-metric limit isomorphism preserves the core slot of every label**, for
labellings transported along it (`ValencyThreeCoreSlots.slot_transport`, at valency four). -/
theorem slot_transport4 {w w' : Regrowth core y degree} {block block'}
    (H : RegrowthAnchor4 w block) (H' : RegrowthAnchor4 w' block') {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (ψ : GeometricDatumIso w.limit w'.limit)
    (hψ : IsMetricIso w w' ψ) (L : Labelling4 w.limit (anchorOf w block))
    (L' : Labelling4 w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) (i : Fin 4) :
    w'.frame.ident.row (pathOf4 L' H'.compat i) = w.frame.ident.row (pathOf4 L H.compat i) := by
  have hQ : NonDanglingEdge.stablePath
      (⟨L'.e i, ((mem_ndAt _ _ _).mp (L'.mem i)).1⟩ : NonDanglingEdge w'.limit) =
      ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) (NonDanglingEdge.stablePath
        (⟨L.e i, ((mem_ndAt _ _ _).mp (L.mem i)).1⟩ : NonDanglingEdge w.limit)) := by
    refine Eq.trans ?_ (GeometricDatumIso.stablePathEquiv_mk ψ _ _).symm
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext (hL i))
  rw [pathOf4_eq_inRow H' L' i, hQ, row_inRow_map w w' (wallRows4 H) (wallRows4 H') hpt ψ hψ]
  rfl

/-- **Stage 3 at valency four, universal form**: at a core with no slot parallel to `e₀`,
along *every* labelled-metric isomorphism of two anchored regrowths' limits, transported
labellings read the same partner. -/
theorem partner_eq_of_metricIso {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hpar : NoParallel core e₀) {w w' : Regrowth core y degree} {block block'}
    (H : RegrowthAnchor4 w block) (H' : RegrowthAnchor4 w' block')
    (ψ : GeometricDatumIso w.limit w'.limit) (hψ : IsMetricIso w w' ψ)
    (L : Labelling4 w.limit (anchorOf w block)) (L' : Labelling4 w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) {s s' : Split4} (hs : Reads4 L s)
    (hs' : Reads4 L' s') : s.partner = s'.partner := by
  obtain ⟨P⟩ := ValencyFourSplit.shape w.frame.fullDim H
  obtain ⟨P'⟩ := ValencyFourSplit.shape w'.frame.fullDim H'
  have h0 : Paired4 L 0 s.partner := (paired4_zero_iff L w.frame.fullDim H hs _).mpr (Or.inr rfl)
  have h1 := (paired4_iff_coreShare L w.frame.ident H.compat P
    (row_e₁ (frameOfBridge P) hpt.1) hpar 0 s.partner).mp h0
  rw [← slot_transport4 H H' hpt ψ hψ L L' hL 0,
    ← slot_transport4 H H' hpt ψ hψ L L' hL s.partner] at h1
  have h2 := (paired4_iff_coreShare L' w'.frame.ident H'.compat P'
    (row_e₁ (frameOfBridge P') hpt.1) hpar 0 s.partner).mpr h1
  rcases (paired4_zero_iff L' w'.frame.fullDim H' hs' _).mp h2 with h | h
  · exact absurd h hs.1
  · exact h

theorem split4_eq {s s' : Split4} (h1 : s.partner = s'.partner) (h2 : s.K = s'.K) : s = s' := by
  cases s; cases s'; simp_all

/-- **Anchored uniqueness at valency four (stages 3--5, every class)**: over a connected core
with at least three vertices and no slot parallel to the vanishing slot, two anchored
regrowths at a facet point whose limits are labelled-metric isomorphic and which read the
same `K` are one class. -/
theorem frameClass_eq_of_metricIso4 (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hpar : NoParallel core e₀)
    (w w' : Regrowth core y degree) {block block'}
    (H : RegrowthAnchor4 w block) (H' : RegrowthAnchor4 w' block')
    (hsame : ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ)
    (hK : ∀ (L : Labelling4 w.limit (anchorOf w block))
      (L' : Labelling4 w'.limit (anchorOf w' block')) (s s' : Split4),
      Reads4 L s → Reads4 L' s' → s.K = s'.K) :
    FrameClass.mk w.frame = FrameClass.mk w'.frame := by
  obtain ⟨ψ, hψ⟩ := hsame
  obtain ⟨L⟩ := ValencyFourSplit.nonempty_labelling4 _ _ H.nd4
  obtain ⟨L', s, s', hL, -, hs, hs', -, -, -⟩ :=
    ValencyFourSplit.regrowth_reads4 w w' H H' e₀ hpt ψ L
  have hss : s = s' := split4_eq (partner_eq_of_metricIso hpt hpar H H' ψ hψ L L' hL hs hs')
    (hK L L' s s' hs hs')
  subst hss
  exact frameClass_eq_of_reads4 hconn hn hpt w w' H H' ψ hψ L L' hL hs hs'

variable {c c' : Core n p} {m : MetricFacetLimit c c' y degree}

/-- **`K`-injectivity on the near side** at every valency-four metric limit of a connected
core with at least three vertices and no slot parallel to the vanishing slot. -/
theorem kIndexL_injective (hconn : c.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hpar : NoParallel c e₀) (hm : V4Limit m) :
    Function.Injective (kIndexL hm e₀ hpt) := by
  intro x x' hxx
  apply Subtype.ext
  obtain ⟨w, hw, hwm⟩ := x.2
  obtain ⟨w', hw', hwm'⟩ := x'.2
  obtain ⟨block, H⟩ := hm.1 w hwm
  obtain ⟨block', H'⟩ := hm.1 w' hwm'
  have hsame : ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ :=
    Quotient.exact (hwm.trans hwm'.symm)
  rw [← hw, ← hw']
  refine frameClass_eq_of_metricIso4 hconn hn hpt hpar w w' H H' hsame
    fun L L' s s' hs hs' ↦ ?_
  rw [← kIndexL_spec hm e₀ hpt x w H L hw hs, ← kIndexL_spec hm e₀ hpt x' w' H' L' hw' hs', hxx]

/-- **`K`-injectivity on the far side.** -/
theorem kIndexR_injective (hconn : c'.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hpar : NoParallel c' e₀) (hm : V4Limit m) :
    Function.Injective (kIndexR hm e₀ hpt) := by
  intro x x' hxx
  apply Subtype.ext
  obtain ⟨w, hw, hwm⟩ := x.2
  obtain ⟨w', hw', hwm'⟩ := x'.2
  obtain ⟨block, H⟩ := hm.2 w hwm
  obtain ⟨block', H'⟩ := hm.2 w' hwm'
  have hsame : ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ :=
    Quotient.exact (hwm.trans hwm'.symm)
  rw [← hw, ← hw']
  refine frameClass_eq_of_metricIso4 hconn hn hpt hpar w w' H H' hsame
    fun L L' s s' hs hs' ↦ ?_
  rw [← kIndexR_spec hm e₀ hpt x w H L hw hs, ← kIndexR_spec hm e₀ hpt x' w' H' L' hw' hs', hxx]

end Injectivity

/-! ## 18.  Walks in a tree read as lists of occurrences: ends, concatenation, reversal -/

section WalkTools

open DraismaVargas.Count.TargetGeodesic

variable {G : CFGraph.{0}}

/-- The vertex a walk read off from `v` arrives at. -/
def walkEnd : G.V → List G.edges → G.V
  | v, [] => v
  | v, e :: rest => walkEnd (otherEndOf e v) rest

theorem walkEnd_append : ∀ (v : G.V) (l₁ l₂ : List G.edges),
    walkEnd v (l₁ ++ l₂) = walkEnd (walkEnd v l₁) l₂
  | _, [], _ => rfl
  | v, e :: rest, l₂ => walkEnd_append (otherEndOf e v) rest l₂

theorem otherEndOf_ne {e : G.edges} {v : G.V} (h : IsEnd e v) : otherEndOf e v ≠ v := by
  have hne := Dart.coe_fst_ne_snd e
  unfold otherEndOf
  split_ifs with h1
  · intro h2; exact hne (h1.trans h2.symm)
  · rcases h with h | h
    · exact absurd h h1
    · intro h2; exact hne (h2.trans h.symm)

theorem otherEndOf_eq_of_ne {e : G.edges} {x y : G.V} (hx : IsEnd e x) (hy : IsEnd e y)
    (hxy : x ≠ y) : otherEndOf e x = y := by
  unfold otherEndOf
  split_ifs with h1
  · rcases hy with h | h
    · exact absurd (h1.symm.trans h) hxy
    · exact h
  · rcases hx with h | h
    · exact absurd h h1
    · rcases hy with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hxy

theorem otherEndOf_otherEndOf {e : G.edges} {v : G.V} (h : IsEnd e v) :
    otherEndOf e (otherEndOf e v) = v :=
  otherEndOf_eq_of_ne (isEnd_otherEndOf e v) h (otherEndOf_ne h)

/-- Concatenation of two walks, joined without backtracking. -/
theorem isWalkFrom_append : ∀ (v : G.V) (l₁ l₂ : List G.edges),
    IsWalkFrom v l₁ → IsWalkFrom (walkEnd v l₁) l₂ →
      (∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, y ≠ x) → IsWalkFrom v (l₁ ++ l₂)
  | _, [], _, _, h₂, _ => h₂
  | v, e :: rest, l₂, h₁, h₂, hseam => by
      refine ⟨h₁.1, ?_, isWalkFrom_append (otherEndOf e v) rest l₂ h₁.2.2 h₂ ?_⟩
      · intro next hnext
        cases rest with
        | nil =>
            exact hseam e (by simp) next (by simpa using hnext)
        | cons r rs =>
            exact h₁.2.1 next (by simpa using hnext)
      · intro x hx y hy
        cases rest with
        | nil => exact absurd hx (by simp)
        | cons r rs =>
            exact hseam x (by rw [List.getLast?_cons_cons]; exact hx) y hy

theorem isEnd_walkEnd_getLast : ∀ (v : G.V) (l : List G.edges) (hne : l ≠ []),
    IsWalkFrom v l → IsEnd (l.getLast hne) (walkEnd v l)
  | _, [], hne, _ => absurd rfl hne
  | v, [e], _, h => by
      show IsEnd e (otherEndOf e v)
      exact isEnd_otherEndOf e v
  | v, e :: r :: rs, _, h => by
      rw [List.getLast_cons_cons]
      exact isEnd_walkEnd_getLast (otherEndOf e v) (r :: rs) (by simp) h.2.2

/-- **The reverse of a walk is a walk**, from its end back to its start. -/
theorem isWalkFrom_reverse : ∀ (v : G.V) (l : List G.edges), IsWalkFrom v l →
    IsWalkFrom (walkEnd v l) l.reverse ∧ walkEnd (walkEnd v l) l.reverse = v
  | _, [], _ => ⟨trivial, rfl⟩
  | v, e :: rest, h => by
      obtain ⟨ih₁, ih₂⟩ := isWalkFrom_reverse (otherEndOf e v) rest h.2.2
      have hEnd : walkEnd v (e :: rest) = walkEnd (otherEndOf e v) rest := rfl
      rw [hEnd, List.reverse_cons]
      refine ⟨isWalkFrom_append _ _ _ ih₁ ?_ ?_, ?_⟩
      · rw [ih₂]
        exact ⟨isEnd_otherEndOf e v, by simp, trivial⟩
      · intro x hx y hy
        have hy' : e = y := by simpa using hy
        subst hy'
        cases rest with
        | nil => exact absurd hx (by simp)
        | cons r rs =>
            have hx' : x = r := by
              rw [List.getLast?_reverse] at hx
              simpa using hx.symm
            subst hx'
            exact fun h' ↦ h.2.1 x rfl h'.symm
      · rw [walkEnd_append, ih₂]
        exact otherEndOf_otherEndOf h.1

/-- **A tree carries no closed walk**, in the list-of-occurrences form. -/
theorem not_closed_walk (hConn : graph_connected G) (hGenus : genus G = 0) {v : G.V}
    {l : List G.edges} (h : IsWalkFrom v l) (hne : l ≠ []) (hEnd : walkEnd v l = v) : False := by
  have hLast := isEnd_walkEnd_getLast v l hne h
  rw [hEnd] at hLast
  match l, hne, h, hLast with
  | [e], _, h, hLast =>
      exact otherEndOf_ne h.1 (by simpa [walkEnd] using hEnd)
  | e :: r :: rs, _, h, hLast =>
      refine not_isEnd_of_mem_tail_of_genusZero hConn hGenus h ?_ hLast
      rw [List.getLast_cons_cons]
      exact List.getLast_mem _

end WalkTools

/-! ## 19.  Walks with backtracking, and their reduction -/

section Trails

open DraismaVargas.Count.TargetGeodesic

variable {G : CFGraph.{0}}

/-- A walk read off from `v` that may backtrack.

It is produced from a source chain by `srcChain_trail` and from a non-backtracking walk
by `isTrailFrom_of_isWalkFrom`, and consumed by `exists_reduce` and `no_split_walk`. -/
def IsTrailFrom : G.V → List G.edges → Prop
  | _, [] => True
  | v, e :: rest => IsEnd e v ∧ IsTrailFrom (otherEndOf e v) rest

/-- **Free reduction**: a walk that may backtrack contains a non-backtracking one with the
same ends. -/
theorem exists_reduce : ∀ (v : G.V) (l : List G.edges), IsTrailFrom v l →
    ∃ l', (∀ e ∈ l', e ∈ l) ∧ IsWalkFrom v l' ∧ walkEnd v l' = walkEnd v l
  | v, [], _ => ⟨[], by simp, trivial, rfl⟩
  | v, e :: rest, h => by
      obtain ⟨r, hsub, hw, hend⟩ := exists_reduce (otherEndOf e v) rest h.2
      have hend' : walkEnd v (e :: rest) = walkEnd (otherEndOf e v) rest := rfl
      cases r with
      | nil =>
          refine ⟨[e], by simp, ⟨h.1, by simp, trivial⟩, ?_⟩
          rw [hend', ← hend]
          rfl
      | cons x r' =>
          by_cases hx : x = e
          · subst hx
            have hv : otherEndOf x (otherEndOf x v) = v := otherEndOf_otherEndOf h.1
            refine ⟨r', fun z hz ↦ List.mem_cons_of_mem _ (hsub z (List.mem_cons_of_mem _ hz)),
              ?_, ?_⟩
            · have h3 := hw.2.2
              rw [hv] at h3
              exact h3
            · rw [hend', ← hend]
              show walkEnd v r' = walkEnd (otherEndOf x (otherEndOf x v)) r'
              rw [hv]
          · refine ⟨e :: x :: r', ?_, ⟨h.1, ?_, hw⟩, ?_⟩
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (hsub z hz)
            · intro next hnext
              have : next = x := by simpa using hnext.symm
              rw [this]
              exact hx
            · rw [hend', ← hend]
              rfl

theorem isTrailFrom_of_isWalkFrom : ∀ (v : G.V) (l : List G.edges), IsWalkFrom v l →
    IsTrailFrom v l
  | _, [], _ => trivial
  | v, e :: rest, h => ⟨h.1, isTrailFrom_of_isWalkFrom (otherEndOf e v) rest h.2.2⟩

/-- **Two non-backtracking walks joined at one turn cannot go from one end of an occurrence
to the other while avoiding it at both ends.**  Both halves avoid `t` (a walk never touches its
start again), so free reduction and `t` close a non-backtracking walk. -/
theorem no_split_walk (hConn : graph_connected G) (hGenus : genus G = 0) {x z : G.V}
    (hxz : x ≠ z) {t : G.edges} (htx : IsEnd t x) (htz : IsEnd t z) (L₁ L₂ : List G.edges)
    (h₁ : IsWalkFrom x L₁) (h₂ : IsWalkFrom (walkEnd x L₁) L₂)
    (hT : IsTrailFrom x (L₁ ++ L₂)) (hEnd : walkEnd x (L₁ ++ L₂) = z)
    (hHead : ∀ e ∈ (L₁ ++ L₂).head?, e ≠ t) (hLast : ∀ e ∈ (L₁ ++ L₂).getLast?, e ≠ t) :
    False := by
  have hnot1 : t ∉ L₁ := by
    cases L₁ with
    | nil => simp
    | cons h r =>
        intro hm
        rcases List.mem_cons.mp hm with hh | hr
        · exact hHead h (by simp) hh.symm
        · exact not_isEnd_of_mem_tail_of_genusZero hConn hGenus h₁ hr htx
  have hnot2 : t ∉ L₂ := by
    obtain ⟨hrev, -⟩ := isWalkFrom_reverse _ L₂ h₂
    rw [← walkEnd_append, hEnd] at hrev
    intro hm
    cases hr : L₂.reverse with
    | nil =>
        rw [List.reverse_eq_nil_iff] at hr
        rw [hr] at hm
        exact absurd hm (by simp)
    | cons h r =>
        rw [hr] at hrev
        have hlast : (L₁ ++ L₂).getLast? = some h := by
          rw [List.getLast?_append, ← List.head?_reverse, hr]
          simp
        have hm' : t ∈ h :: r := by rw [← hr]; exact List.mem_reverse.mpr hm
        rcases List.mem_cons.mp hm' with hh | hr'
        · exact hLast h hlast hh.symm
        · exact not_isEnd_of_mem_tail_of_genusZero hConn hGenus hrev hr' htz
  obtain ⟨l', hsub, hw, hend⟩ := exists_reduce x (L₁ ++ L₂) hT
  rw [hEnd] at hend
  have hnot : t ∉ l' := fun hm ↦ by
    rcases List.mem_append.mp (hsub t hm) with h | h
    · exact hnot1 h
    · exact hnot2 h
  have hwalk : IsWalkFrom x (l' ++ [t]) := by
    refine isWalkFrom_append x l' [t] hw ?_ ?_
    · rw [hend]
      exact ⟨htz, by simp, trivial⟩
    · intro a ha b hb
      have hb' : b = t := by simpa using hb.symm
      rw [hb']
      intro hta
      exact hnot (hta ▸ List.mem_of_getLast? ha)
  refine not_closed_walk hConn hGenus hwalk (by simp) ?_
  rw [walkEnd_append, hend]
  exact otherEndOf_eq_of_ne htz htx (Ne.symm hxz)

/-- **A list whose only non-injective steps all use one pair splits into two injective
halves.** -/
theorem exists_split_turnFree {α β : Type*} (f : α → β) (R : α → α → Prop) :
    ∀ (l : List α), l.Nodup → l.IsChain R → (∀ a b, R a b → a ≠ b) →
    (∀ x ∈ l, ∀ x' ∈ l, ∀ y ∈ l, ∀ y' ∈ l, R x x' → f x = f x' → R y y' → f y = f y' →
      (y = x ∨ y = x') ∧ (y' = x ∨ y' = x')) →
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.IsChain (fun a b ↦ f a ≠ f b) ∧
      l₂.IsChain (fun a b ↦ f a ≠ f b)
  | [], _, _, _, _ => ⟨[], [], rfl, List.isChain_nil, List.isChain_nil⟩
  | [a], _, _, _, _ => ⟨[a], [], rfl, List.isChain_singleton _, List.isChain_nil⟩
  | a :: b :: r, hnd, hc, hR, hK => by
      have hab := (List.isChain_cons_cons.mp hc).1
      have hc' := (List.isChain_cons_cons.mp hc).2
      have ha : a ∉ b :: r := (List.nodup_cons.mp hnd).1
      by_cases hf : f a = f b
      · refine ⟨[a], b :: r, rfl, List.isChain_singleton _, ?_⟩
        refine hc'.imp_of_mem_imp ?_
        intro u u' hu hu' huu' hfu
        obtain ⟨h1, h2⟩ := hK a (by simp) b (by simp) u (List.mem_cons_of_mem _ hu) u'
          (List.mem_cons_of_mem _ hu') hab hf huu' hfu
        have hne := hR u u' huu'
        rcases h1 with rfl | rfl
        · exact ha hu
        · rcases h2 with rfl | rfl
          · exact ha hu'
          · exact hne rfl
      · obtain ⟨l₁, l₂, heq, hc₁, hc₂⟩ := exists_split_turnFree f R (b :: r)
          (List.nodup_cons.mp hnd).2 hc' hR
          (fun x hx x' hx' y hy y' hy' ↦ hK x (List.mem_cons_of_mem _ hx) x'
            (List.mem_cons_of_mem _ hx') y (List.mem_cons_of_mem _ hy) y'
            (List.mem_cons_of_mem _ hy'))
        cases l₁ with
        | nil =>
            refine ⟨[a], b :: r, rfl, List.isChain_singleton _, ?_⟩
            rw [heq]
            simpa using hc₂
        | cons h t =>
            have hh : h = b := by
              have := congrArg List.head? heq
              simp at this
              exact this.symm
            subst hh
            refine ⟨a :: h :: t, l₂, ?_, List.isChain_cons_cons.mpr ⟨hf, hc₁⟩, hc₂⟩
            rw [heq]
            rfl

end Trails

/-! ## 20.  Stable rows as source chains, and the turns of a row -/

section SourceChains

open DraismaVargas.Count.TargetGeodesic
open DraismaVargas.Count.RowGeodesic (isEnd_of_incident otherEndOf_eq not_three_survivors)

variable {target : CFGraph.{0}} {degree : ℕ} (data : GluingDatum target degree)

/-- **A chain of source occurrences entered at `V`**: each is incident to the vertex the
previous one leaves by, and every vertex strictly inside the chain has surviving valency two.

It is produced by the stable-row traversal `W4StableSource.traverse` (`traverse_srcChain`),
and consumed by `srcChain_trail`, `srcChain_walk` and `noParallel_of_anchor4`. -/
def SrcChain : data.SourceVertex → List data.SourceEdge → Prop
  | _, [] => True
  | V, e :: rest => Incident data e V ∧
      (rest ≠ [] → nonDanglingValency data (otherEnd data e V) = 2) ∧
      SrcChain (otherEnd data e V) rest

/-- The vertex a source chain leaves by. -/
def srcEnd : data.SourceVertex → List data.SourceEdge → data.SourceVertex
  | V, [] => V
  | V, e :: rest => srcEnd (otherEnd data e V) rest

theorem srcEnd_append : ∀ (V : data.SourceVertex) (l₁ l₂ : List data.SourceEdge),
    srcEnd data V (l₁ ++ l₂) = srcEnd data (srcEnd data V l₁) l₂
  | _, [], _ => rfl
  | V, e :: r, l₂ => srcEnd_append (otherEnd data e V) r l₂

theorem traverse_srcChain (visited : Finset data.SourceEdge) (edge : data.SourceEdge)
    (vertex : data.SourceVertex) (h : Incident data edge vertex) :
    SrcChain data vertex (traverse data visited edge vertex) := by
  revert h
  refine traverse_rec (motive := fun visited edge vertex ↦ Incident data edge vertex →
    SrcChain data vertex (traverse data visited edge vertex)) ?_ ?_ ?_ visited edge vertex
  · intro visited edge vertex hv _
    rw [traverse_of_mem data vertex hv]
    trivial
  · intro visited edge vertex hv hval h
    rw [traverse_of_valency_ne data hv hval]
    exact ⟨h, fun h' ↦ absurd rfl h', trivial⟩
  · intro visited edge vertex hv hval ih h
    rw [traverse_of_valency_eq data hv hval]
    exact ⟨h, fun _ ↦ hval, ih (stepEdge_incident data hval edge)⟩

theorem srcChain_append : ∀ (V : data.SourceVertex) (l₁ l₂ : List data.SourceEdge),
    SrcChain data V (l₁ ++ l₂) → SrcChain data V l₁ ∧ SrcChain data (srcEnd data V l₁) l₂
  | _, [], _, h => ⟨trivial, h⟩
  | V, e :: r, l₂, h => by
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨ih1, ih2⟩ := srcChain_append (otherEnd data e V) r l₂ h3
      exact ⟨⟨h1, fun hr ↦ h2 (fun h' ↦ hr (List.append_eq_nil_iff.mp h').1), ih1⟩, ih2⟩

theorem nd_srcEnd : ∀ (V : data.SourceVertex) (l₁ : List data.SourceEdge) (e : data.SourceEdge)
    (l₂ : List data.SourceEdge), SrcChain data V (l₁ ++ e :: l₂) → l₁ ≠ [] →
    nonDanglingValency data (srcEnd data V l₁) = 2
  | _, [], _, _, _, hne => absurd rfl hne
  | V, [x], e, l₂, h, _ => h.2.1 (by simp)
  | V, x :: y :: r, e, l₂, h, _ =>
      nd_srcEnd (otherEnd data x V) (y :: r) e l₂ h.2.2 (by simp)

theorem srcChain_isChain : ∀ (V : data.SourceVertex) (l : List data.SourceEdge),
    SrcChain data V l → l.IsChain fun e e' ↦ ∃ M : data.SourceVertex,
      Incident data e M ∧ Incident data e' M ∧ nonDanglingValency data M = 2
  | _, [], _ => List.isChain_nil
  | _, [_], _ => List.isChain_singleton _
  | V, e :: e' :: r, h => List.isChain_cons_cons.mpr
      ⟨⟨otherEnd data e V, incident_otherEnd data e V, h.2.2.1, h.2.1 (by simp)⟩,
        srcChain_isChain (otherEnd data e V) (e' :: r) h.2.2⟩

theorem srcChain_trail : ∀ (V : data.SourceVertex) (l : List data.SourceEdge),
    SrcChain data V l →
    IsTrailFrom V.1.1 (l.map fun e ↦ (e.1.1 : target.edges)) ∧
      walkEnd V.1.1 (l.map fun e ↦ (e.1.1 : target.edges)) = (srcEnd data V l).1.1
  | _, [], _ => ⟨trivial, rfl⟩
  | V, e :: r, h => by
      obtain ⟨ih1, ih2⟩ := srcChain_trail (otherEnd data e V) r h.2.2
      have hO := otherEndOf_eq (data := data) h.1
      refine ⟨⟨isEnd_of_incident h.1, ?_⟩, ?_⟩
      · rw [hO]; exact ih1
      · show walkEnd (otherEndOf (e.1.1 : target.edges) V.1.1) _ = _
        rw [hO]; exact ih2

theorem srcChain_walk : ∀ (V : data.SourceVertex) (l : List data.SourceEdge),
    SrcChain data V l → l.IsChain (fun e e' ↦ (e.1.1 : target.edges) ≠ e'.1.1) →
    IsWalkFrom V.1.1 (l.map fun e ↦ (e.1.1 : target.edges))
  | _, [], _, _ => trivial
  | V, e :: r, h, hc => by
      have hO := otherEndOf_eq (data := data) h.1
      refine ⟨isEnd_of_incident h.1, ?_, ?_⟩
      · intro next hnext
        cases r with
        | nil => exact absurd hnext (by simp)
        | cons e' r' =>
            have : next = (e'.1.1 : target.edges) := by simpa using hnext.symm
            rw [this]
            exact Ne.symm (List.isChain_cons_cons.mp hc).1
      · rw [hO]
        exact srcChain_walk (otherEnd data e V) r h.2.2 (List.IsChain.tail hc)

theorem isChain_ne_and {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Nodup → l.IsChain R → l.IsChain fun a b ↦ a ≠ b ∧ R a b
  | [], _, _ => List.isChain_nil
  | [_], _, _ => List.isChain_singleton _
  | a :: b :: r, hnd, hc => by
      refine List.isChain_cons_cons.mpr ⟨⟨fun h ↦ ?_, (List.isChain_cons_cons.mp hc).1⟩,
        isChain_ne_and (List.nodup_cons.mp hnd).2 (List.isChain_cons_cons.mp hc).2⟩
      exact (List.nodup_cons.mp hnd).1 (by rw [h]; exact List.mem_cons_self)

end SourceChains

section Turns

open DraismaVargas.Count.LeafFibre (leafSurvivors mem_leafSurvivors coreVertex
  nonDanglingValency_coreVertex incident_coreVertex_of_mem_leafSurvivors
  stablePath_eq_of_mem_leafSurvivors leafSurvivor leafSurvivor_spec leafRow
  leafRow_ne_of_noLeafToLeafEdge)
open DraismaVargas.Count.IndexPattern (target_mem_of_incident localRamification_le_targetChange
  targetChange_eq_three_sub_valency)
open DraismaVargas.Count.RowWalk (target_ne_of_localRamification_le_one)
open DraismaVargas.Count.RowGeodesic (not_three_survivors)

variable {target : CFGraph.{0}} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate] {data : GluingDatum target degree}
  (fd : FullDimensionalSourcePresentation data coordinate)

include fd in
/-- **A row turns only over a leaf** (Part I, `prop-local`): two surviving occurrences at a
surviving-valency-two vertex over one target occurrence force local ramification two there,
hence a leaf below. -/
theorem isLeaf_of_turn {M : data.SourceVertex} (hM : nonDanglingValency data M = 2)
    {x x' : data.SourceEdge} (hx : ¬ IsDangling data x) (hxM : Incident data x M)
    (hx' : ¬ IsDangling data x') (hx'M : Incident data x' M) (hne : x ≠ x')
    (hT : x.1.1 = x'.1.1) : IsLeafVertex target M.1.1 := by
  by_contra hNotLeaf
  refine target_ne_of_localRamification_le_one fd.danglingEdgeNoGlue hM ?_ hx hxM hx' hx'M hne hT
  have hMem : x.1.1 ∈ GluingDatum.incidentEdges M.1.1 := target_mem_of_incident hxM
  have hLe := localRamification_le_targetChange fd (wall := M.1.1) ⟨M.1.2, M.2⟩
  rw [targetChange_eq_three_sub_valency fd M.1.1] at hLe
  have hCardPos : 0 < (GluingDatum.incidentEdges M.1.1).card := Finset.card_pos.mpr ⟨_, hMem⟩
  have hne1 : (GluingDatum.incidentEdges M.1.1).card ≠ 1 := hNotLeaf
  omega

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem mem_leafSurvivors_of_incident {v : target.V} (hLeaf : IsLeafVertex target v)
    {x : data.SourceEdge} (hx : ¬ IsDangling data x)
    (hxv : x.1.1 ∈ GluingDatum.incidentEdges v) : x ∈ leafSurvivors (data := data) hLeaf :=
  (mem_leafSurvivors hLeaf).mpr ⟨hx, eq_leafEdge_of_mem hLeaf hxv⟩

include fd in
/-- **A row turns at most once, and always at one pair**: two turns of one stable row use the
same two occurrences (the two survivors of its leaf; distinct leaves have distinct leaf rows). -/
theorem turn_pairs {path : StablePath data} {x x' y y' : data.SourceEdge}
    (hx : ¬ IsDangling data x) (hx' : ¬ IsDangling data x')
    (hy : ¬ IsDangling data y) (hy' : ¬ IsDangling data y')
    (hxp : NonDanglingEdge.stablePath ⟨x, hx⟩ = path)
    (hyp : NonDanglingEdge.stablePath ⟨y, hy⟩ = path)
    {Mx My : data.SourceVertex} (hMx : nonDanglingValency data Mx = 2)
    (hxM : Incident data x Mx) (hx'M : Incident data x' Mx) (hxx : x ≠ x')
    (hTx : x.1.1 = x'.1.1)
    (hMy : nonDanglingValency data My = 2)
    (hyM : Incident data y My) (hy'M : Incident data y' My) (hyy : y ≠ y')
    (hTy : y.1.1 = y'.1.1) :
    (y = x ∨ y = x') ∧ (y' = x ∨ y' = x') := by
  classical
  have hLx := isLeaf_of_turn fd hMx hx hxM hx' hx'M hxx hTx
  have hLy := isLeaf_of_turn fd hMy hy hyM hy' hy'M hyy hTy
  have hxS := mem_leafSurvivors_of_incident hLx hx (target_mem_of_incident hxM)
  have hyS := mem_leafSurvivors_of_incident hLy hy (target_mem_of_incident hyM)
  have hv : Mx.1.1 = My.1.1 := by
    by_contra hne
    apply leafRow_ne_of_noLeafToLeafEdge fd (noLeafToLeafEdge_of_fullDimensional fd) hLx hLy hne
    unfold leafRow
    rw [← stablePath_eq_of_mem_leafSurvivors fd hLx hxS hx,
      ← stablePath_eq_of_mem_leafSurvivors fd hLy hyS hy, hxp, hyp]
  have hmem : ∀ z : data.SourceEdge, ¬ IsDangling data z → Incident data z My →
      z = x ∨ z = x' := by
    intro z hz hzM
    have hzv : z.1.1 ∈ GluingDatum.incidentEdges Mx.1.1 := by
      rw [hv]; exact target_mem_of_incident hzM
    have hzS := mem_leafSurvivors_of_incident hLx hz hzv
    have hx'S := mem_leafSurvivors_of_incident hLx hx' (target_mem_of_incident hx'M)
    by_contra hzz
    push Not at hzz
    exact not_three_survivors (nonDanglingValency_coreVertex fd hLx) hxx (Ne.symm hzz.1)
      (Ne.symm hzz.2) hx (incident_coreVertex_of_mem_leafSurvivors fd hLx hxS) hx'
      (incident_coreVertex_of_mem_leafSurvivors fd hLx hx'S) hz
      (incident_coreVertex_of_mem_leafSurvivors fd hLx hzS)
  exact ⟨hmem y hy hyM, hmem y' hy' hy'M⟩

end Turns

/-! ## 21.  A row of a full-dimensional cover is two geodesics joined at one turn -/

section SplitRow

open DraismaVargas.Count.TargetGeodesic

variable {target : CFGraph.{0}} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate] {data : GluingDatum target degree}
  (fd : FullDimensionalSourcePresentation data coordinate)

include fd in
/-- **The target walk of a stable row, between two of its survivors at vertices of surviving
valency other than two**, is two non-backtracking walks joined at one turn (Part I,
`prop-local` and `rem-leaves-min-change`: a row turns only over a leaf, and distinct leaves have
distinct leaf rows).  It starts by the target occurrence of the first survivor and ends by that
of the second. -/
theorem exists_split_row {X Z : data.SourceVertex} (hX : nonDanglingValency data X ≠ 2)
    (hZ : nonDanglingValency data Z ≠ 2) (g g' : NonDanglingEdge data)
    (hgX : Incident data g.1 X) (hg'Z : Incident data g'.1 Z)
    (hpath : g'.stablePath = g.stablePath) (hne : g'.1 ≠ g.1) :
    ∃ L₁ L₂ : List target.edges, IsWalkFrom X.1.1 L₁ ∧ IsWalkFrom (walkEnd X.1.1 L₁) L₂ ∧
      IsTrailFrom X.1.1 (L₁ ++ L₂) ∧ walkEnd X.1.1 (L₁ ++ L₂) = Z.1.1 ∧
      (L₁ ++ L₂).head? = some (g.1.1.1 : target.edges) ∧
      (L₁ ++ L₂).getLast? = some (g'.1.1.1 : target.edges) := by
  classical
  obtain ⟨l, hl⟩ : ∃ l, l = traverse data ∅ g.1 X := ⟨_, rfl⟩
  have hSC : SrcChain data X l := by rw [hl]; exact traverse_srcChain _ ∅ g.1 _ hgX
  have hnd : l.Nodup := by rw [hl]; exact (traverse_nodup_notMem _ ∅ g.1 _).1
  have hrow : ∀ e ∈ l, ∃ hs : ¬ IsDangling data e,
      NonDanglingEdge.stablePath ⟨e, hs⟩ = g.stablePath := by
    intro e he
    rw [hl] at he
    exact traverse_stablePath _ ∅ g.1 _ g.2 e he
  have hPE : IsPathEnd data g.1 X := ⟨hgX, hX⟩
  have hg'mem : g'.1 ∈ l := by
    rw [hl]; exact mem_traverse_of_stablePath_eq _ hPE g' hpath
  have hhead : l.head? = some g.1 := by
    rw [hl]; exact traverse_head?_eq_some _ ∅ g.1 _ (by simp)
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg'mem
  have hpre : pre ≠ [] := by
    rintro rfl
    rw [hsplit] at hhead
    exact hne (by simpa using hhead)
  have hSCs : SrcChain data X (pre ++ g'.1 :: post) := by rw [← hsplit]; exact hSC
  have hSC2 := srcChain_append _ _ pre (g'.1 :: post) hSCs
  have hE2 := nd_srcEnd _ _ pre g'.1 post hSCs hpre
  have hZo : Z = otherEnd data g'.1 (srcEnd data X pre) := by
    rcases eq_or_eq_otherEnd data hSC2.2.1 hg'Z with h | h
    · rw [h] at hZ
      exact absurd hE2 hZ
    · exact h
  have hl' : l = (pre ++ [g'.1]) ++ post := by rw [hsplit]; simp
  have hSC' : SrcChain data X (pre ++ [g'.1]) :=
    (srcChain_append _ _ (pre ++ [g'.1]) post (by rw [← hl']; exact hSC)).1
  have hend' : srcEnd data X (pre ++ [g'.1]) = Z := by
    rw [srcEnd_append]
    exact hZo.symm
  have hnd' : (pre ++ [g'.1]).Nodup :=
    List.Nodup.sublist (List.sublist_append_left _ post) (hl' ▸ hnd)
  have hsub : ∀ e ∈ pre ++ [g'.1], e ∈ l := fun e he ↦ by
    rw [hl']; exact List.mem_append_left _ he
  have hchain := isChain_ne_and hnd' (srcChain_isChain _ _ _ hSC')
  obtain ⟨l₁, l₂, heq, hc₁, hc₂⟩ := exists_split_turnFree
    (fun e : data.SourceEdge ↦ (e.1.1 : target.edges))
    (fun e e' ↦ e ≠ e' ∧ ∃ M : data.SourceVertex, Incident data e M ∧
      Incident data e' M ∧ nonDanglingValency data M = 2)
    (pre ++ [g'.1]) hnd' hchain (fun _ _ h ↦ h.1)
    (by
      intro x hx x' hx' u hu u' hu' hxx' hTx huu' hTu
      obtain ⟨hxx, Mx, hxM, hx'M, hMx⟩ := hxx'
      obtain ⟨huu, Mu, huM, hu'M, hMu⟩ := huu'
      obtain ⟨hxs, hxp⟩ := hrow x (hsub x hx)
      obtain ⟨hx's, -⟩ := hrow x' (hsub x' hx')
      obtain ⟨hus, hup⟩ := hrow u (hsub u hu)
      obtain ⟨hu's, -⟩ := hrow u' (hsub u' hu')
      exact turn_pairs fd hxs hx's hus hu's hxp hup hMx hxM hx'M hxx hTx hMu huM hu'M huu hTu)
  have hS12 := srcChain_append _ _ l₁ l₂ (by rw [← heq]; exact hSC')
  have hW₁ := srcChain_walk _ _ l₁ hS12.1 hc₁
  have hW₂ := srcChain_walk _ _ l₂ hS12.2 hc₂
  obtain ⟨-, hwe₁⟩ := srcChain_trail _ _ l₁ hS12.1
  obtain ⟨hT, hwe⟩ := srcChain_trail _ _ _ hSC'
  rw [hend'] at hwe
  have hH : ((pre ++ [g'.1]).map fun e : data.SourceEdge ↦ (e.1.1 : target.edges)).head? =
      some (g.1.1.1 : target.edges) := by
    rw [List.head?_map]
    have : (pre ++ [g'.1]).head? = some g.1 := by
      rw [List.head?_append_of_ne_nil _ hpre, ← hhead, hsplit,
        List.head?_append_of_ne_nil _ hpre]
    rw [this]
    rfl
  have hL : ((pre ++ [g'.1]).map fun e : data.SourceEdge ↦ (e.1.1 : target.edges)).getLast? =
      some (g'.1.1.1 : target.edges) := by simp
  rw [heq, List.map_append] at hT hwe hH hL
  exact ⟨_, _, hW₁, by rw [hwe₁]; exact hW₂, hT, hwe, hH, hL⟩

end SplitRow

/-! ## 22.  Geodesic uniqueness, and no closed row at a branch vertex through two directions -/

section Loops

open DraismaVargas.Count.TargetGeodesic

variable {G : CFGraph.{0}}

/-- **Geodesic uniqueness in a tree**: two non-backtracking walks from one vertex to one vertex
are equal. -/
theorem walk_eq_of_walkEnd_eq (hConn : graph_connected G) (hGenus : genus G = 0) :
    ∀ (z : G.V) (W W' : List G.edges), IsWalkFrom z W → IsWalkFrom z W' →
      walkEnd z W = walkEnd z W' → W = W'
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, h', hend => (not_closed_walk hConn hGenus h' (by simp) hend.symm).elim
  | _, _ :: _, [], h, _, hend => (not_closed_walk hConn hGenus h (by simp) hend).elim
  | z, e :: r, e' :: r', h, h', hend => by
      by_cases hee : e = e'
      · subst hee
        rw [walk_eq_of_walkEnd_eq hConn hGenus (otherEndOf e z) r r' h.2.2 h'.2.2 hend]
      · exfalso
        obtain ⟨hrev, hback⟩ := isWalkFrom_reverse z (e :: r) h
        have hw : IsWalkFrom (walkEnd z (e :: r)) ((e :: r).reverse ++ e' :: r') := by
          refine isWalkFrom_append _ _ _ hrev (by rw [hback]; exact h') ?_
          intro x hx u hu
          have hx' : x = e := by
            rw [List.getLast?_reverse] at hx
            simpa using hx.symm
          have hu' : u = e' := by simpa using hu.symm
          rw [hx', hu']
          exact Ne.symm hee
        refine not_closed_walk hConn hGenus hw (by simp) ?_
        rw [walkEnd_append, hback]
        exact hend.symm

/-- **Two non-backtracking walks joined at one turn do not close up through two different
directions** at their common start. -/
theorem no_split_loop (hConn : graph_connected G) (hGenus : genus G = 0) {x : G.V}
    (L₁ L₂ : List G.edges) (h₁ : IsWalkFrom x L₁) (h₂ : IsWalkFrom (walkEnd x L₁) L₂)
    (hEnd : walkEnd x (L₁ ++ L₂) = x) {e e' : G.edges} (hH : (L₁ ++ L₂).head? = some e)
    (hL : (L₁ ++ L₂).getLast? = some e') (hee : e ≠ e') : False := by
  cases L₁ with
  | nil =>
      refine not_closed_walk hConn hGenus h₂ ?_ hEnd
      rintro rfl
      simp at hH
  | cons a r =>
      cases L₂ with
      | nil =>
          exact not_closed_walk hConn hGenus h₁ (by simp) (by simpa using hEnd)
      | cons b r' =>
          obtain ⟨hrev, hback⟩ := isWalkFrom_reverse _ (b :: r') h₂
          have hz : walkEnd (walkEnd x (a :: r)) (b :: r') = x := by
            rw [← walkEnd_append]; exact hEnd
          rw [hz] at hrev hback
          have heq := walk_eq_of_walkEnd_eq hConn hGenus x (a :: r) (b :: r').reverse h₁ hrev
            hback.symm
          have h1 : e = a := by simpa using hH.symm
          have h2 : (b :: r').getLast? = some e' := by
            rw [List.getLast?_append_of_ne_nil _ (by simp)] at hL
            exact hL
          have h3 : ((b :: r').reverse).head? = some e' := by rw [List.head?_reverse]; exact h2
          rw [← heq] at h3
          exact hee (h1.trans (by simpa using h3))

end Loops

/-! ## 23.  At a valency-four facet the core has no loop at the anchor: no slot parallel to
the vanishing slot, and no self-loop at either of its ends -/

section NoParallel4

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyThreeSplit (ndAt mem_ndAt fib)
open ValencyThreeCoreSlots (NoParallel vertexOf coreIncidence_vertexOf vertexOf_end row_e₁)
open ValencyThreeLoopMerge (LoopAtEnd)
open ValencyFourSplit (RegrowthAnchor4 Bridge)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The row of a slot other than `e₀`, at a branch vertex of the anchor fibre, meets it by
survivors off the contracted occurrence (`Bridge.ndOver_eq`: the only survivor there over the
contracted occurrence is the bridge, whose row is `e₀`). -/
theorem not_contracted_of_row (w : Regrowth core y degree) {block}
    (H : RegrowthAnchor4 w block) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (P : Bridge w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) block) {f : Fin p} (hf : f ≠ e₀)
    (g : NonDanglingEdge w.frame.data) (X : w.frame.data.SourceVertex)
    (hX : X ∈ fib w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) block)
    (hI : Incident w.frame.data g.1 X) (hg : g.stablePath = w.frame.ident.row.symm f) :
    g.1.1.1 ≠ w.frame.edgeOf w.column := by
  intro hT
  have hmem : g.1 ∈ ValencyThreeSplit.ndOver w.frame.data X (w.frame.edgeOf w.column) :=
    (ValencyThreeSplit.mem_ndOver _ _ _ _).mpr ⟨(mem_ndAt _ _ _).mpr ⟨g.2, hI⟩, hT⟩
  rw [P.ndOver_eq w.frame.fullDim H hX] at hmem
  have heq : g.1 = P.e₁ := Finset.mem_singleton.mp hmem
  apply hf
  have h1 : w.frame.ident.row g.stablePath = f := by
    rw [hg]; exact w.frame.ident.row.apply_symm_apply f
  have h2 : g.stablePath = NonDanglingEdge.stablePath
      ⟨(frameOfBridge P).e₁, ValencyThreeCoreSlots.e₁_survives (frameOfBridge P)⟩ :=
    congrArg NonDanglingEdge.stablePath (Subtype.ext heq)
  rw [← h1, h2]
  exact row_e₁ (frameOfBridge P) hpt.1

/-- **At a valency-four facet no core slot is parallel to the vanishing slot.**  A slot `f`
meeting both ends of `e₀` would be an incoming stable row from the branch vertex `R` (over the
end `a` of the contracted occurrence `t₁`) to the other branch vertex `Y` (over `b`), leaving
`R` and entering `Y` by labelled survivors, hence by target occurrences other than `t₁`
(`not_contracted_of_row`).  Its target walk is two geodesics joined at one turn
(`exists_split_row`); such a walk from `a` to `b` avoids `t₁` at both ends, and `t₁` would
close a non-backtracking walk in the target tree (`no_split_walk`). -/
theorem noParallel_of_anchor4 (w : Regrowth core y degree) {block}
    (H : RegrowthAnchor4 w block) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y) :
    NoParallel core e₀ := by
  classical
  intro f hf
  by_contra hb
  push Not at hb
  obtain ⟨hbt, hbh⟩ := hb
  obtain ⟨P⟩ := ValencyFourSplit.shape w.frame.fullDim H
  have he₁ := row_e₁ (frameOfBridge P) hpt.1
  have hR3 : nonDanglingValency w.frame.data (w.frame.data.sourceEnds P.e₁).1 = 3 := P.nd_fst
  have hY3 : nonDanglingValency w.frame.data (w.frame.data.sourceEnds P.e₁).2 = 3 := P.nd_snd
  have hvR : vertexOf w.frame.ident (w.frame.data.sourceEnds P.e₁).1 hR3 = core.tail e₀ ∨
      vertexOf w.frame.ident (w.frame.data.sourceEnds P.e₁).1 hR3 = core.head e₀ :=
    vertexOf_end (frameOfBridge P) w.frame.ident he₁ _ (Or.inl rfl) hR3
  have hvY : vertexOf w.frame.ident (w.frame.data.sourceEnds P.e₁).2 hY3 = core.tail e₀ ∨
      vertexOf w.frame.ident (w.frame.data.sourceEnds P.e₁).2 hY3 = core.head e₀ :=
    vertexOf_end (frameOfBridge P) w.frame.ident he₁ _ (Or.inr rfl) hY3
  have hposR : 0 < coreIncidence core (vertexOf w.frame.ident _ hR3) f := by
    rcases hvR with h | h <;> rw [h] <;> omega
  have hposY : 0 < coreIncidence core (vertexOf w.frame.ident _ hY3) f := by
    rcases hvY with h | h <;> rw [h] <;> omega
  have hcR : 0 < StablePathCount.incidenceCount w.frame.data (w.frame.data.sourceEnds P.e₁).1
      (w.frame.ident.row.symm f) := by
    have h := coreIncidence_vertexOf w.frame.ident _ hR3 (w.frame.ident.row.symm f)
    rw [Equiv.apply_symm_apply] at h
    rw [← h]; exact hposR
  have hcY : 0 < StablePathCount.incidenceCount w.frame.data (w.frame.data.sourceEnds P.e₁).2
      (w.frame.ident.row.symm f) := by
    have h := coreIncidence_vertexOf w.frame.ident _ hY3 (w.frame.ident.row.symm f)
    rw [Equiv.apply_symm_apply] at h
    rw [← h]; exact hposY
  obtain ⟨gR, hgRi, hgRp⟩ := (StablePathCount.incidenceCount_pos_iff _ _ _).mp hcR
  obtain ⟨gY, hgYi, hgYp⟩ := (StablePathCount.incidenceCount_pos_iff _ _ _).mp hcY
  have hncR := not_contracted_of_row w H hpt P hf gR _ P.fst_mem hgRi hgRp
  have hncY := not_contracted_of_row w H hpt P hf gY _ P.snd_mem hgYi hgYp
  have hne : gY.1 ≠ gR.1 := by
    intro hh
    apply P.ends_ne
    refine ValencyFourSplit.eq_of_mem_ndAt_of_mem_ndAt hncR P.fst_mem P.snd_mem
      ((mem_ndAt _ _ _).mpr ⟨gR.2, hgRi⟩) ?_
    rw [← hh]
    exact (mem_ndAt _ _ _).mpr ⟨gY.2, hgYi⟩
  obtain ⟨L₁, L₂, hW₁, hW₂, hT, hwe, hH, hL⟩ := exists_split_row w.frame.fullDim
    (by rw [hR3]; norm_num) (by rw [hY3]; norm_num) gR gY hgRi hgYi (hgYp.trans hgRp.symm) hne
  exact no_split_walk w.frame.fullDim.targetConnected w.frame.fullDim.targetGenus
    (x := (w.frame.data.sourceEnds P.e₁).1.1.1) (z := (w.frame.data.sourceEnds P.e₁).2.1.1)
    (by rw [P.fst_over, P.snd_over]; exact fst_ne_snd _)
    (t := w.frame.edgeOf w.column) (Or.inl P.fst_over.symm) (Or.inr P.snd_over.symm) _ _
    hW₁ hW₂ hT hwe (fun e he ↦ by rw [hH] at he; rw [← Option.mem_some_iff.mp he]; exact hncR)
    (fun e he ↦ by rw [hL] at he; rw [← Option.mem_some_iff.mp he]; exact hncY)

/-- **At a valency-four facet the core has no self-loop at an end of the vanishing slot.**  A
self-loop at the core vertex of the branch vertex `R` would be a stable row leaving `R` and
returning to it by its two labelled survivors, which lie over two different target
occurrences (`R` is unramified); two geodesics joined at one turn cannot do that
(`no_split_loop`). -/
theorem not_loopAtEnd_of_anchor4 (w : Regrowth core y degree) {block}
    (H : RegrowthAnchor4 w block) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y) :
    ¬ LoopAtEnd core e₀ := by
  classical
  rintro ⟨f, hloop, hend⟩
  obtain ⟨P⟩ := ValencyFourSplit.shape w.frame.fullDim H
  have he₁ := row_e₁ (frameOfBridge P) hpt.1
  -- the branch vertex over the looped core vertex
  obtain ⟨X, hXmem, hX3, hvX⟩ : ∃ X, X ∈ fib w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) block ∧ ∃ h3 : nonDanglingValency w.frame.data X = 3,
      vertexOf w.frame.ident X h3 = core.tail f := by
    have hR3 : nonDanglingValency w.frame.data (w.frame.data.sourceEnds P.e₁).1 = 3 := P.nd_fst
    have hY3 : nonDanglingValency w.frame.data (w.frame.data.sourceEnds P.e₁).2 = 3 := P.nd_snd
    have hvR : vertexOf w.frame.ident (w.frame.data.sourceEnds P.e₁).1 hR3 = core.tail e₀ ∨
        vertexOf w.frame.ident (w.frame.data.sourceEnds P.e₁).1 hR3 = core.head e₀ :=
      vertexOf_end (frameOfBridge P) w.frame.ident he₁ _ (Or.inl rfl) hR3
    have hvY : vertexOf w.frame.ident (w.frame.data.sourceEnds P.e₁).2 hY3 = core.tail e₀ ∨
        vertexOf w.frame.ident (w.frame.data.sourceEnds P.e₁).2 hY3 = core.head e₀ :=
      vertexOf_end (frameOfBridge P) w.frame.ident he₁ _ (Or.inr rfl) hY3
    have hvne : vertexOf w.frame.ident _ hR3 ≠ vertexOf w.frame.ident _ hY3 := fun h ↦
      P.ends_ne (congrArg Subtype.val (w.frame.ident.vertex.injective h))
    -- the two branch vertices sit over the two ends of `e₀`, which are distinct
    have hcases : core.tail f = vertexOf w.frame.ident _ hR3 ∨
        core.tail f = vertexOf w.frame.ident _ hY3 := by
      rcases hend with h | h <;> rcases hvR with h1 | h1 <;> rcases hvY with h2 | h2
      all_goals first
        | exact Or.inl (h.trans h1.symm)
        | exact Or.inr (h.trans h2.symm)
        | exact absurd (h1.trans h2.symm) hvne
    rcases hcases with h | h
    · exact ⟨_, P.fst_mem, hR3, h.symm⟩
    · exact ⟨_, P.snd_mem, hY3, h.symm⟩
  have hf : f ≠ e₀ := by
    rintro rfl
    -- `e₀` has two distinct ends in the core
    have hR3 : nonDanglingValency w.frame.data (w.frame.data.sourceEnds P.e₁).1 = 3 := P.nd_fst
    have hY3 : nonDanglingValency w.frame.data (w.frame.data.sourceEnds P.e₁).2 = 3 := P.nd_snd
    have hvR := vertexOf_end (frameOfBridge P) w.frame.ident he₁ _ (Or.inl rfl) hR3
    have hvY := vertexOf_end (frameOfBridge P) w.frame.ident he₁ _ (Or.inr rfl) hY3
    rw [← hloop, or_self] at hvR hvY
    exact P.ends_ne (congrArg Subtype.val (w.frame.ident.vertex.injective (hvR.trans hvY.symm)))
  -- the row of `f` meets `X` twice
  have hc2 : StablePathCount.incidenceCount w.frame.data X (w.frame.ident.row.symm f) = 2 := by
    have h := coreIncidence_vertexOf w.frame.ident X hX3 (w.frame.ident.row.symm f)
    rw [Equiv.apply_symm_apply, hvX] at h
    rw [← h]
    unfold coreIncidence
    rw [if_pos rfl, if_pos hloop.symm]
  unfold StablePathCount.incidenceCount at hc2
  obtain ⟨g, hg, g', hg', hgg⟩ := Finset.one_lt_card.mp (by rw [hc2]; norm_num)
  obtain ⟨hgi, hgp⟩ := Finset.mem_filter.mp hg
  obtain ⟨hg'i, hg'p⟩ := Finset.mem_filter.mp hg'
  rw [StablePathCount.mem_incidentEdges] at hgi hg'i
  have hne : g'.1 ≠ g.1 := fun h ↦ hgg (Subtype.ext h).symm
  have hncg := not_contracted_of_row w H hpt P hf g X hXmem hgi hgp
  have hncg' := not_contracted_of_row w H hpt P hf g' X hXmem hg'i hg'p
  -- the two survivors lie over different target occurrences (`X` is unramified)
  have htne : (g.1.1.1 : w.frame.target.edges) ≠ g'.1.1.1 := by
    intro hT
    have hlabel : ∀ h : NonDanglingEdge w.frame.data, Incident w.frame.data h.1 X →
        h.1 ∈ ndAt w.frame.data X := fun h hi ↦ (mem_ndAt _ _ _).mpr ⟨h.2, hi⟩
    exact hne (ValencyThreeSplit.eq_of_ram_zero w.frame.data w.frame.fullDim
      (ValencyFourSplit.ram_eq_zero_of_mem_fib w.frame.fullDim H hXmem) (hlabel g' hg'i)
      (hlabel g hgi) hT.symm)
  obtain ⟨L₁, L₂, hW₁, hW₂, hT, hwe, hH, hL⟩ := exists_split_row w.frame.fullDim
    (by rw [hX3]; norm_num) (by rw [hX3]; norm_num) g g' hgi hg'i (hg'p.trans hgp.symm) hne
  exact no_split_loop w.frame.fullDim.targetConnected w.frame.fullDim.targetGenus L₁ L₂ hW₁ hW₂
    hwe hH hL htne

end NoParallel4

/-! ## 24.  `K`-injectivity at every valency-four metric limit, and the census inputs -/

section InjectivityFinal

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyFourSplit (V4Limit kIndexL kIndexR RegrowthAnchor4 Labelling4)
open ValencyThreeGeneral (MetricFacetLimit)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open CensusAssembly (ResolvedDatum V4InputsSupply V2ClauseSupply)

variable {n p degree : ℕ} {c c' : Core n p} {y : Fin p → ℚ} {m : MetricFacetLimit c c' y degree}

/-- **`K`-injectivity on the near side, unconditionally at a valency-four metric limit** of a
connected core with at least three vertices: the no-parallel-slot hypothesis of
`kIndexL_injective` holds at every such limit (`noParallel_of_anchor4`), so no loop merge is
needed at valency four. -/
theorem kIndexL_injective_of_v4 (hconn : c.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hm : V4Limit m) :
    Function.Injective (kIndexL hm e₀ hpt) := by
  intro x x' hxx
  obtain ⟨w, -, hwm⟩ := x.2
  obtain ⟨block, H⟩ := hm.1 w hwm
  exact kIndexL_injective hconn hn hpt (noParallel_of_anchor4 w H hpt) hm hxx

/-- **`K`-injectivity on the far side**, likewise. -/
theorem kIndexR_injective_of_v4 (hconn : c'.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hm : V4Limit m) :
    Function.Injective (kIndexR hm e₀ hpt) := by
  intro x x' hxx
  obtain ⟨w, -, hwm⟩ := x.2
  obtain ⟨block, H⟩ := hm.2 w hwm
  exact kIndexR_injective hconn hn hpt (noParallel_of_anchor4 w H hpt) hm hxx

/-- **The two injectivity conjuncts of `CensusAssembly.V4InputsSupply`** at every resolved
datum (indeed only its facet point is used). -/
theorem injective_of_resolved {c c' : CubicCore n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}
    (R : ResolvedDatum c c' degree e₀ y₀ ε) (hn : 3 ≤ n)
    (m : MetricFacetLimit c.core c'.core y₀ degree) (hm : V4Limit m) :
    Function.Injective (kIndexL hm e₀ R.datum.point) ∧
      Function.Injective (kIndexR hm e₀ R.datum.point) :=
  ⟨kIndexL_injective_of_v4 c.connected hn R.datum.point hm,
    kIndexR_injective_of_v4 c'.connected hn R.datum.point hm⟩

/-- **`V4InputsSupply` from per-`K` realisation alone**: the injectivity conjuncts are
proved, so the valency-four input of the census assembly is exactly the realisation of every
admissible `K` on both sides. -/
theorem v4InputsSupply_of_realisation (hn : 3 ≤ n)
    (hex : ∀ (c c' : CubicCore n p) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ)
      (R : ResolvedDatum c c' degree e₀ y₀ ε) (m : MetricFacetLimit c.core c'.core y₀ degree)
      (hm : V4Limit m),
      (∀ (w₀ : Regrowth c.core y₀ degree), MetricFacetLimit.ofLeft (c' := c'.core) w₀ = m →
        ∀ {block₀} (_ : RegrowthAnchor4 w₀ block₀)
          (L₀ : Labelling4 w₀.limit (ValencyThreeSplit.anchorOf w₀ block₀)) (K : ℕ),
          L₀.indices.KAdmissible K →
            (∃ x, kIndexL hm e₀ R.datum.point x = K) ∧ ∃ x, kIndexR hm e₀ R.datum.point x = K) ∧
      (∀ (w₀ : Regrowth c'.core y₀ degree), MetricFacetLimit.ofRight (c := c.core) w₀ = m →
        ∀ {block₀} (_ : RegrowthAnchor4 w₀ block₀)
          (L₀ : Labelling4 w₀.limit (ValencyThreeSplit.anchorOf w₀ block₀)) (K : ℕ),
          L₀.indices.KAdmissible K →
            (∃ x, kIndexL hm e₀ R.datum.point x = K) ∧ ∃ x, kIndexR hm e₀ R.datum.point x = K)) :
    V4InputsSupply n p degree := fun c c' e₀ y₀ ε R m hm ↦
  ⟨(injective_of_resolved R hn m hm).1, (injective_of_resolved R hn m hm).2,
    (hex c c' e₀ y₀ ε R m hm).1, (hex c c' e₀ y₀ ε R m hm).2⟩

end InjectivityFinal

end DraismaVargas.Count.ValencyFourRigidity
