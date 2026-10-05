module

public import DraismaVargasCount.W4NonDiscreteStarCensus
public import DraismaVargasCount.M11StarExhaustionProof
public import DraismaVargas.LocalCases.DanglingDescent

@[expose] public section

/-!
# Non-discrete W4 exhaustion, and the `w4` clause of `FamilyStarParity` with no hypothesis

Source: Draisma--Vargas Part I (arXiv:1909.12924): the inherited properties of limits
(the target expansion and the limit matrix, `lemma-class-union`,
`lemma-limit-matrix-change`) and the auxiliary cases `{aux-r0-nd2}`, `{aux-r0-nd3}` that
produce the members of Equation (1); Vargas, Part II (arXiv:2609.09109): the star of a
codimension-one wall and `prop-signed-mult`.  The residue proved here is the one
isolated in `W4NonDiscreteStarCensus`; the builder is
`M11StarExhaustionProof.nonempty_transportFree_of_rel`.  This completes the W4 case of
the star parity in step 2 of `Assembly`.

## The result, in one paragraph

`W4NonDiscreteStarCensus.W4NonDiscreteStarExhaustion` is proved at every degree, core size
and request (`w4NonDiscreteStarExhaustion`).  In fact every star member at *every*
four-valent wall, discrete or not, is a frame isomorph of a nonsingular position of
Equation (1) (`exhausts`, `census`).  Hence `RegrowthWallInput.FamilyStarParity … .w4`
holds with no hypothesis (`familyStarParity_w4`, and `familyStarParity_w4_all` at every
degree).

The proof is `W4NonDiscreteStarCensus.exhausts_of_transports`: one
`ResolutionExpansionFree.TransportFree` per member, at the member's own pairing.  Three
ingredients build it.

1. **The member's resolution.**  Part I's incoming identification
   (`W4IncomingRepresentatives.transported_sameBlocks_*`, fed by
   `W4IncomingPairingReceipts.receiptsOfForest`) holds at every wall.  It says the member's
   read-off resolution has *the same blocks* as its own W4 family's pasted resolution
   (`member_left_sameBlocks`, `member_right_sameBlocks`, `member_newEdge_sameBlocks`).
2. **Both families as relations.**  Each family resolution is written, block by block, as a
   relation that depends only on:
   - the block's active labels (`act`, `eff`);
   - the non-joined side (`ns`);
   - one reference occurrence (`ref`).

   This is `side_rel_iff` and `new_rel_iff` over `SideShape` and `NewShape`.  Both are
   natural along any limit isomorphism (`act_map`, `sideShape_map`, `newShape_map`), with
   explicit block-wise permutations (`sidePerm`, `newPerm`).  The builder of
   `M11StarExhaustionProof` then gives the
   transport as soon as the isomorphism is **coherent**
   (`nonempty_transportFree_of_coherent`).
3. **Coherence by pendant relabelling.**  An arbitrary limit isomorphism is *not* coherent.
   On a non-joined side at a block of size two or more, a star occurrence that dangles on
   the block (the inactive fourth label of an nd3 block, or the second inactive label of a
   same-side nd2 block) may be permuted against the reference occurrence.  Such an
   isomorphism admits no transport, because `endpoint_compatible` fails.

   The repair is an automorphism of the *wall's* limit.  It fixes every branch vertex and
   every stable path, and re-points each such pendant (`beta`, `betaAll`, `coherentIso`).
   `coherent_coherentIso` proves the result coherent.  The automorphism exists because:
   - every occurrence inside a dangling side is dangling
     (`nonempty_danglingSide_of_mem_side`);
   - the dangling side of a pendant occurrence contains its whole target branch, sheet by
     sheet (`nonempty_farSide`, `mem_side_of_vertexMember`);
   - pendant sheets are single sheets on that branch (`blockCard_eq_one_of_forall_isDangling`,
     `pendant_single`);
   - so the region relabelling (`TargetBranchRegion`, `SheetRelabeling.ofRegion`) fixes
     every partition there (`relabel_eq_self`, `pendantIso`, `pendantLimitIso`).

   Entirely dangling wall blocks need no repair: they are single sheets
   (`eq_of_act_empty`).

## What is proved

* §1 `exists_sub_side`, `nonempty_danglingSide_of_mem_side` (graph).
* §2 `sourceEnds_sourceEdge`, `isDangling_of_incident_side`,
  `nonDanglingValency_eq_zero_of_mem_side`, `nonempty_farSide`, `mem_side_of_vertexMember`,
  `incidentEdges_nonempty`, `blockCard_eq_one_of_forall_isDangling`, `pendant_*`.
* §3 `relabel_eq_self`, `pendantRelabeling`, `pendantIso`, `pendantIso_branch`,
  `pendantIso_row`.
* §4 `eff`, `ns`, `ref` and their finite facts (`decide`); `nd2_side_rel`, `nd2_new_rel`,
  `nd3_side_rel`, `nd3_new_rel`; `act`, `SideShape`, `NewShape`, `pattern_cases`,
  `side_rel_iff`, `new_rel_iff`.
* §5 `sourceEdgeEquiv_sourceEdge`, `vertexPerm_rel_iff`, `edgePerm_rel_iff`,
  `edgePerm_rel_vertexPerm`, `act_le`, `act_map`, `act_eq_of_rel`, `sideShape_map`,
  `newShape_map`; `sideFun`, `newFun`, `sidePerm`, `newPerm`.
* §6 `Coherent`, `nonempty_transportFree_of_coherent`.
* §7 `limit_changeMinimalAt`, `limit_noDanglingTargetFibres`.
* §8 `pendantDatum`, `pendantLimitIso`.  §9 `eq_of_act_empty`.
* §10 `memberInput`, `memberReceipts`, `member_*_sameBlocks`.
* §11 `Adj`, `adjFun`, `adjPerm`, `adj_pendant`, `beta`, `betaAll`, `coherentIso`
  (with `coherentIso_inheritedStar`, `coherentIso_index`, both `rfl`), `phi`,
  `coherent_coherentIso`.
* §12 `nonempty_positionTransport`, `exhausts`, `census`, **`w4NonDiscreteStarExhaustion`**,
  **`familyStarParity_w4_all`**, **`familyStarParity_w4`**.

## What is NOT proved

* Nothing is assumed: every headline has no hypothesis beyond its binders.
* `Coherent` is a property of one limit isomorphism, not a supply.  It is a hypothesis only
  of the intermediate `nonempty_transportFree_of_coherent`, and `coherent_coherentIso`
  discharges it for every member.  The member's *given* limit isomorphism is not claimed to
  be coherent: the proof replaces it.
* No other family is treated.  §§1--3 and §8 (pendant relabelling) are family-generic.  So
  is the coherence mechanism: any family whose non-joined side carries a dangling occurrence
  can re-point it the same way.
-/

namespace DraismaVargas.Count.W4NonDiscreteStarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open W4StableSource DanglingDescent StableLocalProperties

/-! ## 1.  Every occurrence inside a dangling side is dangling -/

section Graph

universe u

variable {G : CFGraph.{u}}

/-- Every vertex of a dangling side other than its inner endpoint lies in the
strictly smaller dangling side of some occurrence at the inner endpoint. -/
theorem exists_sub_side {i o : G.V} (cut : DanglingSide G i o) {x : G.V}
    (hx : x ∈ cut.side) (hne : x ≠ i) :
    ∃ w : G.V, ∃ c : DanglingSide G w i, c.side.card < cut.side.card ∧ x ∈ c.side := by
  have hReach := reach_of_graph_connected cut.side_connected ⟨i, cut.left_mem⟩ ⟨x, hx⟩
  suffices h : ∀ z, Reach (Utilities.inducedSubgraph G cut.side ⟨i, cut.left_mem⟩)
      ⟨i, cut.left_mem⟩ z → z.1 = i ∨
        ∃ w : G.V, ∃ c : DanglingSide G w i, c.side.card < cut.side.card ∧ z.1 ∈ c.side by
    rcases h _ hReach with h | h
    · exact absurd h hne
    · exact h
  intro z hz
  induction hz with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
      have hbc' : 0 < num_edges G b.1 c.1 := by
        have h := Utilities.num_edges_inducedSubgraph G cut.side ⟨i, cut.left_mem⟩ b c
        exact lt_of_lt_of_eq hbc h
      obtain ⟨bv, hbm⟩ := b
      obtain ⟨cv, hcm⟩ := c
      change 0 < num_edges G bv cv at hbc'
      change bv = i ∨ _ at ih
      change cv = i ∨ ∃ w : G.V, ∃ c : DanglingSide G w i,
        c.side.card < cut.side.card ∧ cv ∈ c.side
      rcases ih with hb | ⟨w, cw, hcard, hbw⟩
      · subst hb
        obtain ⟨smaller, hsm⟩ := exists_danglingSide_of_mem_side cut hcm hbc'
        exact Or.inr ⟨cv, smaller, hsm, smaller.left_mem⟩
      · by_cases hcw : cv ∈ cw.side
        · exact Or.inr ⟨w, cw, hcard, hcw⟩
        · have hCross := cw.cross_num_edges bv cv hbw hcw
          by_cases hPair : bv = w ∧ cv = i
          · exact Or.inl hPair.2
          · rw [ite_eq_right hPair] at hCross
            omega

/-- **Every occurrence between two vertices of a dangling side carries a
dangling side itself**, in one of the two orientations. -/
theorem nonempty_danglingSide_of_mem_side :
    ∀ (n : ℕ) {i o : G.V} (cut : DanglingSide G i o), cut.side.card ≤ n →
      ∀ {a b : G.V}, a ∈ cut.side → b ∈ cut.side → 0 < num_edges G a b →
        Nonempty (DanglingSide G a b) ∨ Nonempty (DanglingSide G b a) := by
  intro n
  induction n with
  | zero =>
      intro i o cut hcard
      have := Finset.card_pos.mpr ⟨i, cut.left_mem⟩
      omega
  | succ n ih =>
      intro i o cut hcard a b ha hb hab
      by_cases hai : a = i
      · subst hai
        obtain ⟨smaller, -⟩ := exists_danglingSide_of_mem_side cut hb hab
        exact Or.inr ⟨smaller⟩
      by_cases hbi : b = i
      · subst hbi
        obtain ⟨smaller, -⟩ := exists_danglingSide_of_mem_side cut ha
          (by rwa [num_edges_symmetric])
        exact Or.inl ⟨smaller⟩
      obtain ⟨w, c, hcard', haw⟩ := exists_sub_side cut ha hai
      have hbw : b ∈ c.side := by
        by_contra hbw
        have hCross := c.cross_num_edges a b haw hbw
        rw [ite_eq_right fun h ↦ hbi h.2] at hCross
        omega
      exact ih c (by omega) haw hbw hab

end Graph

/-! ## 2.  Pendant sheets beyond a star occurrence -/

section Pendant

open TargetSeparation TargetBranchRegion

variable {T : CFGraph} {d : ℕ} (D : GluingDatum T d)

/-- The endpoint of a canonical source occurrence, read at either end, is the endpoint of
its own sheet (the edge partition refines both vertex partitions). -/
theorem sourceEnds_sourceEdge (f : T.edges) (s : Fin d) :
    D.sourceEnds (D.sourceEdge f s) =
      (D.sourceEndpoint (f : T.V × T.V).1 s, D.sourceEndpoint (f : T.V × T.V).2 s) := by
  refine Prod.ext ?_ ?_
  · apply (D.sourceEndpoint_eq_iff _ _ _).mpr
    refine ⟨rfl, ?_⟩
    change (D.vertexPartition _).Rel ((D.edgePartition f).repr s)
      ((D.vertexPartition _).repr s)
    exact (D.refines_left f).rel ((D.edgePartition f).rel_repr_left s) |>.trans
      ((D.vertexPartition _).rel_repr_right s)
  · apply (D.sourceEndpoint_eq_iff _ _ _).mpr
    refine ⟨rfl, ?_⟩
    change (D.vertexPartition _).Rel ((D.edgePartition f).repr s)
      ((D.vertexPartition _).repr s)
    exact (D.refines_right f).rel ((D.edgePartition f).rel_repr_left s) |>.trans
      ((D.vertexPartition _).rel_repr_right s)

/-- **Every occurrence incident to a vertex of a dangling side is dangling.** -/
theorem isDangling_of_incident_side {L R : D.SourceVertex}
    (cut : DanglingSide D.sourceGraph L R) {v : D.SourceVertex} (hv : v ∈ cut.side)
    {g : D.SourceEdge} (hInc : Incident D g v) : IsDangling D g := by
  obtain ⟨w, hEnds⟩ := exists_other_sourceEnd D hInc
  have hPos : 0 < num_edges D.sourceGraph v w := num_edges_pos_of_sourceEnds D hEnds
  have hSide : Nonempty (DanglingSide D.sourceGraph v w) ∨
      Nonempty (DanglingSide D.sourceGraph w v) := by
    by_cases hw : w ∈ cut.side
    · exact nonempty_danglingSide_of_mem_side _ cut le_rfl hv hw hPos
    · have hCross := cut.cross_num_edges v w hv hw
      by_cases hPair : v = L ∧ w = R
      · obtain ⟨rfl, rfl⟩ := hPair
        exact Or.inl ⟨cut⟩
      · split_ifs at hCross with h'
        · exact absurd h' hPair
        · omega
  unfold IsDangling
  rcases hEnds with h | h <;> rw [h] <;> simp only
  · exact hSide
  · exact hSide.symm

/-- No surviving occurrence at a vertex of a dangling side. -/
theorem nonDanglingValency_eq_zero_of_mem_side {L R : D.SourceVertex}
    (cut : DanglingSide D.sourceGraph L R) {v : D.SourceVertex} (hv : v ∈ cut.side) :
    nonDanglingValency D v = 0 := by
  classical
  rw [← card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro g _ hSurv
  exact hSurv (isDangling_of_incident_side D cut hv g.2)

variable {A : T.V} {e : T.edges} (he : (e : T.V × T.V).1 = A ∨ (e : T.V × T.V).2 = A)

include he in
/-- **Orientation.**  A dangling star occurrence whose near endpoint carries a surviving
occurrence hangs its tree on the far side. -/
theorem nonempty_farSide (s : Fin d) (hDang : IsDangling D (D.sourceEdge e s))
    (hNear : ∃ g : D.SourceEdge, ¬ IsDangling D g ∧ Incident D g (D.sourceEndpoint A s)) :
    Nonempty (DanglingSide D.sourceGraph (D.sourceEndpoint (farEndpoint A e) s)
      (D.sourceEndpoint A s)) := by
  obtain ⟨g, hg, hgInc⟩ := hNear
  have hEnds := sourceEnds_sourceEdge D e s
  unfold IsDangling at hDang
  rcases farEndpoint_ends he with hE | hE <;> rw [hE] at hEnds <;> simp only at hEnds <;>
    rw [hEnds] at hDang <;> simp only at hDang
  · rcases hDang with h | h
    · obtain ⟨c⟩ := h
      exact absurd (isDangling_of_incident_side D c c.left_mem hgInc) hg
    · exact h
  · rcases hDang with h | h
    · exact h
    · obtain ⟨c⟩ := h
      exact absurd (isDangling_of_incident_side D c c.left_mem hgInc) hg

include he in
/-- **The whole branch beyond the occurrence lies in its dangling side**, sheet by sheet. -/
theorem mem_side_of_vertexMember (s : Fin d)
    (cut : DanglingSide D.sourceGraph (D.sourceEndpoint (farEndpoint A e) s)
      (D.sourceEndpoint A s))
    {X : T.V} (hX : VertexMember A (farEndpoint A e) (farEndpoint_ne he) X) :
    D.sourceEndpoint X s ∈ cut.side := by
  obtain ⟨hXA, hReach⟩ := hX
  rw [SimpleGraph.reachable_iff_reflTransGen] at hReach
  suffices h : ∀ Y : {v : T.V // v ≠ A},
      Relation.ReflTransGen (deletedGraph A).Adj ⟨farEndpoint A e, farEndpoint_ne he⟩ Y →
        D.sourceEndpoint Y.1 s ∈ cut.side from h _ hReach
  intro Y hY
  induction hY with
  | refl => exact cut.left_mem
  | @tail b c _ hbc ih =>
      have hAdj : 0 < num_edges T b.1 c.1 := hbc
      obtain ⟨pair, hMem, hPair⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos T _ _ hAdj
      obtain ⟨f, hf⟩ := exists_occurrence_of_mem_edges hMem
      have hSrc := sourceEnds_sourceEdge D f s
      have hPos : 0 < num_edges D.sourceGraph (D.sourceEndpoint b.1 s) (D.sourceEndpoint c.1 s) := by
        apply num_edges_pos_of_sourceEnds D (edge := D.sourceEdge f s)
        rw [hSrc, hf]
        rcases hPair with h | h <;> rw [h]
        · exact Or.inl rfl
        · exact Or.inr rfl
      by_contra hc
      have hCross := cut.cross_num_edges _ _ ih hc
      by_cases hP : D.sourceEndpoint b.1 s = D.sourceEndpoint (farEndpoint A e) s ∧
          D.sourceEndpoint c.1 s = D.sourceEndpoint A s
      · have := congrArg (fun v : D.SourceVertex ↦ v.1.1) hP.2
        exact c.2 this
      · split_ifs at hCross with h'
        · exact absurd h' hP
        · omega

end Pendant

/-! ### Pendant sheets are single sheets -/

section Singleton

variable {T : CFGraph} {d : ℕ} (D : GluingDatum T d)

/-- A vertex with a neighbour in a connected target with at least two vertices has an
incident occurrence. -/
theorem incidentEdges_nonempty (hConn : graph_connected T) {X Y : T.V} (hXY : X ≠ Y) :
    (GluingDatum.incidentEdges X).Nonempty := by
  classical
  obtain ⟨v, hv, z, hz, hEdge⟩ := hConn {X} ⟨X, Y, Finset.mem_singleton_self X,
    by simpa [Finset.mem_singleton] using hXY.symm⟩
  rw [Finset.mem_singleton] at hv
  subst hv
  obtain ⟨pair, hMem, hPair⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos T _ _ hEdge
  obtain ⟨f, hf⟩ := exists_occurrence_of_mem_edges hMem
  refine ⟨f, ?_⟩
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hf]
  rcases hPair with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **A source vertex all of whose incident occurrences dangle is a single sheet**, at
a change-minimal target vertex of a valid datum with dangling-no-glue and no dangling
target fibre, in a connected target with another vertex. -/
theorem blockCard_eq_one_of_forall_isDangling (hValid : D.Valid)
    (hNoGlue : DanglingEdgeNoGlue D) (hFibres : NoDanglingTargetFibres D)
    (hConn : graph_connected T) {X Y : T.V} (hXY : X ≠ Y) (hMin : D.ChangeMinimalAt X)
    (s : Fin d) (hDang : ∀ g : D.SourceEdge, Incident D g (D.sourceEndpoint X s) →
      IsDangling D g) :
    (D.vertexPartition X).blockCard s = 1 := by
  classical
  set v := D.sourceEndpoint X s with hvdef
  have hCardRepr : (D.vertexPartition X).blockCard s =
      (D.vertexPartition v.1.1).blockCard v.1.2 := by
    change (D.vertexPartition X).blockCard s =
      (D.vertexPartition X).blockCard ((D.vertexPartition X).repr s)
    unfold SheetPartition.blockCard
    rw [(D.vertexPartition X).block_eq_of_rel ((D.vertexPartition X).rel_repr_right s)]
  rw [hCardRepr]
  have hZeroValency : nonDanglingValency D v = 0 := by
    rw [← card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro g _ hSurv
    exact hSurv (hDang g.1 g.2)
  by_cases hLeaf : (GluingDatum.incidentEdges X).card = 1
  · rcases leaf_block_dichotomy D hValid hFibres X hLeaf hMin ⟨v.1.2, v.2⟩ with
      ⟨_, hOne, _⟩ | ⟨_, _, _, g, hg⟩
    · exact hOne
    · exact absurd (hDang g.1 g.2) hg
  · have hPos := (incidentEdges_nonempty (T := T) hConn hXY).card_pos
    have hForm := localRamification_eq_nonDangling_form D hNoGlue v
    rw [hZeroValency] at hForm
    have hEmpty : ((Finset.univ : Finset (IncidentSourceEdge D v)).filter
        (fun edge ↦ ¬ IsDangling D edge.1)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro g _ hSurv
      exact hSurv (hDang g.1 g.2)
    rw [hEmpty, Finset.sum_empty] at hForm
    have hLe : D.localRamification v.1.1 ⟨v.1.2, v.2⟩ ≤ D.targetChange X := by
      unfold GluingDatum.targetChange
      exact Finset.single_le_sum (f := fun b ↦ D.localRamification X b)
        (fun b _ ↦ D.localRamification_nonneg X (hValid.2 X) b) (Finset.mem_univ _)
    have hMin' := hMin
    unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hMin'
    have hB := (D.vertexPartition v.1.1).blockCard_pos v.1.2
    have hCast : (1 : ℤ) ≤ ((D.vertexPartition v.1.1).blockCard v.1.2 : ℤ) := by exact_mod_cast hB
    have hNe : ((GluingDatum.incidentEdges X).card : ℤ) ≠ 1 := by exact_mod_cast hLeaf
    have hPosZ : (0 : ℤ) < ((GluingDatum.incidentEdges X).card : ℤ) := by exact_mod_cast hPos
    have : ((D.vertexPartition v.1.1).blockCard v.1.2 : ℤ) = 1 := by
      push_cast at hForm
      omega
    exact_mod_cast this

end Singleton

/-! ## 3.  The pendant relabelling: an automorphism of a datum moving one branch -/

section PendantIso

open TargetBranchRegion TargetSeparation GluingDatum

variable {d : ℕ}

/-- A permutation moving only singleton sheets of a partition, and those among
themselves, fixes the partition. -/
theorem relabel_eq_self (P : SheetPartition d) (σ : Equiv.Perm (Fin d))
    (hSingle : ∀ i, σ i ≠ i → ∀ j, P.Rel i j → i = j) : P.relabel σ = P := by
  apply SheetPartition.ext_repr
  funext i
  change σ (P.repr (σ.symm i)) = P.repr i
  by_cases hk : σ.symm i = i
  · rw [hk]
    have hFix : σ i = i := by
      conv_lhs => rw [← hk]
      exact σ.apply_symm_apply i
    by_contra hne
    have h1 := hSingle (P.repr i) hne i (P.rel_repr_left i)
    rw [h1] at hne
    exact hne hFix
  · have hkMoved : σ (σ.symm i) ≠ σ.symm i := by
      rw [Equiv.apply_symm_apply]
      exact fun h ↦ hk h.symm
    have hkRepr : P.repr (σ.symm i) = σ.symm i :=
      (hSingle _ hkMoved _ (P.rel_repr_right (σ.symm i))).symm
    rw [hkRepr, Equiv.apply_symm_apply]
    have hiMoved : σ i ≠ i := by
      intro h
      apply hk
      conv_lhs => rw [← h]
      exact σ.symm_apply_apply i
    exact hSingle i hiMoved _ (P.rel_repr_right i)

end PendantIso

section PendantIsoDatum

open TargetBranchRegion TargetSeparation GluingDatum

variable {T : CFGraph} {d : ℕ} (D : GluingDatum T d) (A root : T.V) (hRoot : root ≠ A)
  (σ : Equiv.Perm (Fin d)) (hInner : ∀ s, (D.vertexPartition A).Rel (σ s) s)

/-- The sheet relabelling that applies `σ` on the branch of `root` at `A`. -/
noncomputable def pendantRelabeling : D.SheetRelabeling :=
  SheetRelabeling.ofRegion (vertexMoved A root hRoot) (edgeMoved A root hRoot) σ
    (fun f h s ↦ by rw [boundary_left A root hRoot f h]; exact hInner s)
    (fun f h s ↦ by rw [boundary_right A root hRoot f h]; exact hInner s)

theorem relabel_toggle (b : Bool) (P : SheetPartition d)
    (h : b = true → P.relabel σ = P) :
    P.relabel (SheetRelabeling.togglePermutation b σ) = P := by
  cases b
  · exact Transport.DatumIso.relabel_refl P
  · exact h rfl

variable (hSingle : ∀ s, σ s ≠ s → ∀ X, vertexMoved A root hRoot X = true →
  ∀ t, (D.vertexPartition X).Rel s t → s = t)

include hSingle in
theorem edge_single (s : Fin d) (hs : σ s ≠ s) (f : T.edges)
    (hf : edgeMoved A root hRoot f = true) (t : Fin d) (hst : (D.edgePartition f).Rel s t) :
    s = t := by
  unfold edgeMoved at hf
  rcases Bool.or_eq_true_iff.mp hf with h | h
  · exact hSingle s hs _ h t ((D.refines_left f).rel hst)
  · exact hSingle s hs _ h t ((D.refines_right f).rel hst)

/-- **The pendant automorphism** of `D`: `σ` on the branch of `root`, the identity
elsewhere. -/
noncomputable def pendantIso : GeometricDatumIso D D where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends _ := Or.inl rfl
  vertexPerm := (pendantRelabeling D A root hRoot σ hInner).vertexPermutation
  edgePerm := (pendantRelabeling D A root hRoot σ hInner).edgePermutation
  vertexPartition X := (relabel_toggle σ _ _ fun h ↦
    relabel_eq_self _ σ fun s hs t hst ↦ hSingle s hs X h t hst).symm
  edgePartition f := (relabel_toggle σ _ _ fun h ↦
    relabel_eq_self _ σ fun s hs t hst ↦
      edge_single D A root hRoot σ hSingle s hs f h t hst).symm
  compatible f v hv s := by
    rcases hv with rfl | rfl
    · exact (pendantRelabeling D A root hRoot σ hInner).compatible_left f s
    · exact (pendantRelabeling D A root hRoot σ hInner).compatible_right f s

theorem pendantIso_vertexPerm (X : T.V) :
    (pendantIso D A root hRoot σ hInner hSingle).vertexPerm X =
      SheetRelabeling.togglePermutation (vertexMoved A root hRoot X) σ := rfl

theorem pendantIso_edgePerm (f : T.edges) :
    (pendantIso D A root hRoot σ hInner hSingle).edgePerm f =
      SheetRelabeling.togglePermutation (edgeMoved A root hRoot f) σ := rfl

variable (hZero : ∀ s, σ s ≠ s → ∀ X, vertexMoved A root hRoot X = true →
  nonDanglingValency D (D.sourceEndpoint X s) = 0)
  (hDang : ∀ g : D.SourceEdge, edgeMoved A root hRoot g.1.1 = true → σ g.1.2 ≠ g.1.2 →
    IsDangling D g)

include hZero in
/-- The pendant automorphism fixes every branch vertex. -/
theorem pendantIso_branch (hConn : D.Connected) (b : StableGraphIncidence.BranchVertex D) :
    (pendantIso D A root hRoot σ hInner hSingle).branchVertexEquiv hConn b = b := by
  apply Subtype.ext
  apply Subtype.ext
  change ((b.1.1.1 : T.V), SheetRelabeling.togglePermutation (vertexMoved A root hRoot b.1.1.1) σ
    b.1.1.2) = b.1.1
  cases hMoved : vertexMoved A root hRoot b.1.1.1
  · rfl
  · change (b.1.1.1, σ b.1.1.2) = b.1.1
    by_cases hs : σ b.1.1.2 = b.1.1.2
    · rw [hs]
    · have h0 := hZero _ hs _ hMoved
      rw [D.sourceEndpoint_self b.1] at h0
      have := b.2
      omega

include hDang in
/-- The pendant automorphism fixes every stable path. -/
theorem pendantIso_row (hConn : D.Connected) (p : StablePath D) :
    (pendantIso D A root hRoot σ hInner hSingle).stablePathEquiv hConn p = p := by
  refine Quot.inductionOn p ?_
  intro g
  change NonDanglingEdge.stablePath _ = NonDanglingEdge.stablePath g
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  change ((g.1.1.1 : T.edges), SheetRelabeling.togglePermutation (edgeMoved A root hRoot g.1.1.1) σ
    g.1.1.2) = g.1.1
  cases hMoved : edgeMoved A root hRoot g.1.1.1
  · rfl
  · change (g.1.1.1, σ g.1.1.2) = g.1.1
    by_cases hs : σ g.1.1.2 = g.1.1.2
    · rw [hs]
    · exact absurd (hDang g.1 hMoved hs) g.2

end PendantIsoDatum

section PendantBundle

open TargetBranchRegion TargetSeparation GluingDatum

variable {T : CFGraph} {d : ℕ} (D : GluingDatum T d) {A : T.V} {e : T.edges}
  (he : (e : T.V × T.V).1 = A ∨ (e : T.V × T.V).2 = A)
  (hValid : D.Valid) (hNoGlue : DanglingEdgeNoGlue D) (hFibres : NoDanglingTargetFibres D)
  (hConn : graph_connected T) (hMin : ∀ X, X ≠ A → D.ChangeMinimalAt X)
  (M : Fin d → Prop)
  (hM : ∀ s, M s → IsDangling D (D.sourceEdge e s) ∧
    ∃ g : D.SourceEdge, ¬ IsDangling D g ∧ Incident D g (D.sourceEndpoint A s))

include he hM in
theorem exists_cut (s : Fin d) (hs : M s) :
    Nonempty (DanglingSide D.sourceGraph (D.sourceEndpoint (farEndpoint A e) s)
      (D.sourceEndpoint A s)) :=
  nonempty_farSide D he s (hM s hs).1 (hM s hs).2

include he hM in
theorem pendant_isDangling (s : Fin d) (hs : M s) {X : T.V}
    (hX : vertexMoved A (farEndpoint A e) (farEndpoint_ne he) X = true)
    (g : D.SourceEdge) (hg : Incident D g (D.sourceEndpoint X s)) : IsDangling D g := by
  obtain ⟨cut⟩ := exists_cut D he M hM s hs
  exact isDangling_of_incident_side D cut
    (mem_side_of_vertexMember D he s cut ((vertexMoved_eq_true_iff _ _ _ _).mp hX)) hg

include he hM in
theorem pendant_zero (s : Fin d) (hs : M s) {X : T.V}
    (hX : vertexMoved A (farEndpoint A e) (farEndpoint_ne he) X = true) :
    nonDanglingValency D (D.sourceEndpoint X s) = 0 := by
  obtain ⟨cut⟩ := exists_cut D he M hM s hs
  exact nonDanglingValency_eq_zero_of_mem_side D cut
    (mem_side_of_vertexMember D he s cut ((vertexMoved_eq_true_iff _ _ _ _).mp hX))

include he hM hValid hNoGlue hFibres hConn hMin in
theorem pendant_single (s : Fin d) (hs : M s) {X : T.V}
    (hX : vertexMoved A (farEndpoint A e) (farEndpoint_ne he) X = true)
    (t : Fin d) (hst : (D.vertexPartition X).Rel s t) : s = t := by
  have hXA : X ≠ A := by
    intro h
    subst h
    rw [vertexMoved_wall] at hX
    exact Bool.false_ne_true hX
  have hOne := blockCard_eq_one_of_forall_isDangling D hValid hNoGlue hFibres hConn hXA
    (hMin X hXA) s (pendant_isDangling D he M hM s hs hX)
  have hBlock := (D.vertexPartition X).block_eq_singleton_of_blockCard_eq_one s hOne
  have hMem : t ∈ (D.vertexPartition X).block s := ((D.vertexPartition X).mem_block_iff s t).mpr hst
  rw [hBlock, Finset.mem_singleton] at hMem
  exact hMem.symm

include he hM in
theorem pendant_edge_isDangling (g : D.SourceEdge)
    (hg : edgeMoved A (farEndpoint A e) (farEndpoint_ne he) g.1.1 = true) (hs : M g.1.2) :
    IsDangling D g := by
  unfold edgeMoved at hg
  rcases Bool.or_eq_true_iff.mp hg with h | h
  · exact pendant_isDangling D he M hM g.1.2 hs h g (Or.inl rfl)
  · exact pendant_isDangling D he M hM g.1.2 hs h g (Or.inr rfl)

end PendantBundle


open W4TargetPairings.Pairing (labelRight)

/-! ## 4.  The shape of a W4 block resolution, as a function of its active labels -/

section Combinatorics

/-- The active set a W4 pattern resolves by: an entirely dangling block is resolved as the
harmless nd2 block `{0, 1}` (`ActiveBlockClassification.danglingBlock`). -/
def eff (act : Finset (Fin 4)) : Finset (Fin 4) := if act = ∅ then {0, 1} else act

/-- The side at which the block's resolution is not the joined one (`none`: joined on both
sides). -/
def ns (a : Finset (Fin 4)) (q : Fin 3) : Option Bool :=
  if a.card = 2 then
    (if (a.filter fun L ↦ labelRight q L = true).card = 2 then some false
     else if (a.filter fun L ↦ labelRight q L = false).card = 2 then some true
     else none)
  else if a.card = 3 then
    (if (a.filter fun L ↦ labelRight q L = true).card = 1 then some true else some false)
  else none

/-- The reference label on the non-joined side: the active singleton of an nd3 block, the
smaller of the two inactive labels of a same-side nd2 block. -/
def ref (a : Finset (Fin 4)) (q : Fin 3) : Fin 4 :=
  ((List.finRange 4).find? fun L ↦
    decide (ns a q = some (labelRight q L) ∧ (L ∈ a ∨ a.card = 2))).getD 0

theorem labelRight_ref (a : Finset (Fin 4)) (q : Fin 3) (v : Bool) (h : ns a q = some v) :
    labelRight q (ref a q) = v := by
  revert a q v
  decide

theorem ref_not_mem_of_card_two (a : Finset (Fin 4)) (q : Fin 3) (v : Bool) (h : ns a q = some v)
    (hCard : a.card = 2) : ref a q ∉ a := by
  revert a q v
  decide

theorem not_mem_of_ne_ref (a : Finset (Fin 4)) (q : Fin 3) (v : Bool) (h : ns a q = some v)
    (L : Fin 4) (hL : labelRight q L = v) (hne : L ≠ ref a q) : L ∉ a := by
  revert a q v L
  decide

theorem ns_pair (f s : Fin 4) (hfs : f ≠ s) (q : Fin 3) :
    ns {f, s} q = (if labelRight q f = labelRight q s then some (!labelRight q f) else none) := by
  revert f s q
  decide

theorem card_pair (f s : Fin 4) (hfs : f ≠ s) : ({f, s} : Finset (Fin 4)).card = 2 := by
  revert f s
  decide

theorem ns_nd3 (blk : W4Assembly.Nd3Block) (q : Fin 3) :
    ns blk.activeLabels q = some (labelRight q (blk.singletonLabel q)) ∧
      ref blk.activeLabels q = blk.singletonLabel q := by
  obtain ⟨f, s, t, h1, h2, h3⟩ := blk
  simp only [W4Assembly.Nd3Block.activeLabels, W4Assembly.Nd3Block.singletonLabel]
  revert f s t q
  decide

theorem eff_of_ne {act : Finset (Fin 4)} (h : act ≠ ∅) : eff act = act := by
  simp [eff, h]

theorem eff_empty : eff ∅ = {0, 1} := rfl

end Combinatorics

section LocalShapes

open DraismaVargas.Infrastructure ResolutionM11 ResolutionW4 ResolutionCoarseFine
open W4OutgoingSurvival (sidePartition)

variable {d : ℕ}

theorem splitBlock_rel_iff' (W : SheetPartition d) {a x : Fin d} (hx : W.Rel a x) (y : Fin d) :
    (W.splitBlock a).Rel x y ↔ W.Rel x y ∧ x = y := by
  rw [W.splitBlock_rel_of_rel_anchor_iff a x hx]
  exact ⟨fun h ↦ ⟨h ▸ rfl, h⟩, fun h ↦ h.2⟩

/-- The side partitions of an nd2 resolution, as relations on the anchor's block. -/
theorem nd2_side_rel (W : SheetPartition d) {a x : Fin d} (hx : W.Rel a x) (y : Fin d)
    (b₁ b₂ side : Bool) (E : SheetPartition d)
    (hE : b₁ = b₂ → W.Rel x y → (E.Rel x y ↔ x = y)) :
    (sidePartition (nd2Resolution W a b₁ b₂) side).Rel x y ↔
      W.Rel x y ∧ ((if b₁ = b₂ then some (!b₁) else none) = some side → E.Rel x y) := by
  have hSplit := splitBlock_rel_iff' W hx y
  cases b₁ <;> cases b₂ <;> cases side <;>
    simp only [nd2Resolution, splitResolutionAt, joinedResolutionAt, LocalResolution.reverse,
      sidePartition, dite_true, dite_false, ite_true, ite_false, Bool.false_eq_true,
      reduceCtorEq, Option.some.injEq, Bool.not_false, Bool.not_true, and_true, true_implies,
      IsEmpty.forall_iff] <;>
    first
    | exact hSplit
    | exact ⟨fun h ↦ h, fun h ↦ h⟩
    | exact ⟨fun h ↦ ⟨(hSplit.mp h).1, (hE rfl (hSplit.mp h).1).mpr (hSplit.mp h).2⟩,
        fun h ↦ hSplit.mpr ⟨h.1, (hE rfl h.1).mp h.2⟩⟩

/-- The new edge of an nd2 resolution, as a relation on the anchor's block. -/
theorem nd2_new_rel (W : SheetPartition d) {a x : Fin d} (hx : W.Rel a x) (y : Fin d)
    (b₁ b₂ : Bool) (E : SheetPartition d)
    (hE : b₁ = b₂ → W.Rel x y → (E.Rel x y ↔ x = y)) :
    (nd2Resolution W a b₁ b₂).newEdge.Rel x y ↔
      W.Rel x y ∧ ((if b₁ = b₂ then some (!b₁) else none) ≠ none → E.Rel x y) := by
  have hSplit := splitBlock_rel_iff' W hx y
  cases b₁ <;> cases b₂ <;>
    simp only [nd2Resolution, splitResolutionAt, joinedResolutionAt, LocalResolution.reverse,
      dite_true, dite_false, ite_true, ite_false, Bool.false_eq_true, reduceCtorEq, ne_eq,
      not_false_eq_true, not_true_eq_false, true_implies, IsEmpty.forall_iff, and_true] <;>
    first
    | exact ⟨fun h ↦ h, fun h ↦ h⟩
    | exact ⟨fun h ↦ ⟨(hSplit.mp h).1, (hE rfl (hSplit.mp h).1).mpr (hSplit.mp h).2⟩,
        fun h ↦ hSplit.mpr ⟨h.1, (hE rfl h.1).mp h.2⟩⟩

/-- The side partitions of an nd3 resolution. -/
theorem nd3_side_rel (W fine : SheetPartition d) (hFine : fine.Refines W) (x y : Fin d)
    (b side : Bool) :
    (sidePartition (nd3Resolution W fine hFine b) side).Rel x y ↔
      W.Rel x y ∧ (some b = some side → fine.Rel x y) := by
  cases b <;> cases side <;>
    simp only [nd3Resolution, fineResolution, LocalResolution.reverse, sidePartition, ite_true,
      ite_false, Bool.false_eq_true, reduceCtorEq, Option.some.injEq, true_implies,
      IsEmpty.forall_iff, and_true] <;>
    first
    | exact ⟨fun h ↦ h, fun h ↦ h⟩
    | exact ⟨fun h ↦ ⟨hFine.rel h, h⟩, fun h ↦ h.2⟩

/-- The new edge of an nd3 resolution. -/
theorem nd3_new_rel (W fine : SheetPartition d) (hFine : fine.Refines W) (x y : Fin d)
    (b : Bool) :
    (nd3Resolution W fine hFine b).newEdge.Rel x y ↔
      W.Rel x y ∧ (some b ≠ none → fine.Rel x y) := by
  rw [nd3Resolution_newEdge]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_implies]
  exact ⟨fun h ↦ ⟨hFine.rel h, h⟩, fun h ↦ h.2⟩

end LocalShapes

section Shape

open DraismaVargas.Infrastructure ResolutionM11 ResolutionW4 W4StableSource W4Assembly
open W4SourceClassification
open W4OutgoingSurvival (sidePartition)

variable {T : CFGraph} {d : ℕ} {A : T.V} (D : GluingDatum T d)
  (S : W4TargetPairings.FourStar T A)

/-- The active labels of the wall block of a sheet. -/
noncomputable def act (x : Fin d) : Finset (Fin 4) := activeLabels D S (WallBlock.ofSheet D A x)

/-- The relational shape of a W4 side partition on the block of `x`. -/
def SideShape (q : Fin 3) (side : Bool) (x y : Fin d) : Prop :=
  (D.vertexPartition A).Rel x y ∧ (ns (eff (act D S x)) q = some side →
    (D.edgePartition (S.edge (ref (eff (act D S x)) q))).Rel x y)

/-- The relational shape of a W4 new-edge partition on the block of `x`. -/
def NewShape (q : Fin 3) (x y : Fin d) : Prop :=
  (D.vertexPartition A).Rel x y ∧ (ns (eff (act D S x)) q ≠ none →
    (D.edgePartition (S.edge (ref (eff (act D S x)) q))).Rel x y)

theorem ofSheet_repr (x : Fin d) :
    WallBlock.ofSheet D A ((D.vertexPartition A).repr x) = WallBlock.ofSheet D A x :=
  Subtype.ext ((D.vertexPartition A).repr_idem x)

/-- An inactive label is a single sheet on the whole block. -/
theorem inactive_rel_iff (hNoGlue : DanglingEdgeNoGlue D) {x y : Fin d} {L : Fin 4}
    (hL : L ∉ act D S x) :
    (D.edgePartition (S.edge L)).Rel x y ↔ x = y := by
  have hOne := blockCard_eq_one_of_not_mem_activeLabels D S hNoGlue (WallBlock.ofSheet D A x) L hL x
    ((D.vertexPartition A).rel_repr_left x)
  constructor
  · intro h
    have hBlock := (D.edgePartition (S.edge L)).block_eq_singleton_of_blockCard_eq_one x hOne
    have hMem : y ∈ (D.edgePartition (S.edge L)).block x :=
      ((D.edgePartition (S.edge L)).mem_block_iff x y).mpr h
    rw [hBlock, Finset.mem_singleton] at hMem
    exact hMem.symm
  · rintro rfl
    rfl

variable (I : AuxR0SourceInput D S) (q : Fin 3)

theorem pattern_cases (x : Fin d) :
    (I.activeProfile.blockPattern ((D.vertexPartition A).repr x) = .nd2 ActiveBlockClassification.danglingBlock ∧
        act D S x = ∅) ∨
      (∃ blk : Nd2Block, I.activeProfile.blockPattern ((D.vertexPartition A).repr x) = .nd2 blk ∧
        blk.activeLabels = act D S x) ∨
      (∃ blk : Nd3Block, I.activeProfile.blockPattern ((D.vertexPartition A).repr x) = .nd3 blk ∧
        blk.activeLabels = act D S x) := by
  unfold ActiveBranchProfile.blockPattern
  rw [ofSheet_repr]
  unfold act
  cases hc : I.activeProfile.classification (WallBlock.ofSheet D A x) with
  | dangling hActive =>
      left
      refine ⟨rfl, ?_⟩
      have h : (∅ : Finset (Fin 4)) = activeLabels D S (WallBlock.ofSheet D A x) := by
        simpa [AuxR0SourceInput.activeProfile, activeBranchProfileOfDanglingNoGlue] using hActive
      exact h.symm
  | nd2 blk hActive =>
      right; left
      refine ⟨blk, rfl, ?_⟩
      simpa [AuxR0SourceInput.activeProfile, activeBranchProfileOfDanglingNoGlue] using hActive
  | nd3 blk hActive =>
      right; right
      refine ⟨blk, rfl, ?_⟩
      simpa [AuxR0SourceInput.activeProfile, activeBranchProfileOfDanglingNoGlue] using hActive

theorem side_rel_iff (hNoGlue : DanglingEdgeNoGlue D) (side : Bool) (x y : Fin d) :
    (sidePartition (wholeResolution D S I.activeProfile.blockPattern q) side).Rel x y ↔
      SideShape D S q side x y := by
  rw [W4OutgoingSurvival.wholeResolution_side_rel]
  have hax : (D.vertexPartition A).Rel ((D.vertexPartition A).repr x) x :=
    (D.vertexPartition A).rel_repr_left x
  unfold blockwiseResolution SideShape
  rcases pattern_cases D S I x with ⟨hp, hact⟩ | ⟨blk, hp, hact⟩ | ⟨blk, hp, hact⟩
  · rw [hp]
    change (sidePartition (nd2Resolution (D.vertexPartition A) _ (S.right q (S.edge 0))
      (S.right q (S.edge 1))) side).Rel x y ↔ _
    rw [W4TargetPairings.FourStar.right_edge, W4TargetPairings.FourStar.right_edge, hact,
      eff_empty, ns_pair 0 1 (by decide)]
    exact nd2_side_rel _ hax y _ _ side _ fun _ _ ↦
      inactive_rel_iff D S hNoGlue (by rw [hact]; exact Finset.notMem_empty _)
  · rw [hp]
    have hne : act D S x ≠ ∅ := by
      rw [← hact]
      exact Finset.nonempty_iff_ne_empty.mp ⟨blk.first, by simp [Nd2Block.activeLabels]⟩
    change (sidePartition (nd2Resolution (D.vertexPartition A) _ (S.right q (S.edge blk.first))
      (S.right q (S.edge blk.second))) side).Rel x y ↔ _
    rw [W4TargetPairings.FourStar.right_edge, W4TargetPairings.FourStar.right_edge, eff_of_ne hne,
      ← hact]
    change _ ↔ _ ∧ (ns {blk.first, blk.second} q = some side → _)
    rw [ns_pair _ _ blk.distinct]
    refine nd2_side_rel _ hax y _ _ side _ fun hb _ ↦ inactive_rel_iff D S hNoGlue ?_
    rw [← hact]
    exact ref_not_mem_of_card_two _ q _ (by change ns {blk.first, blk.second} q = _; rw [ns_pair _ _ blk.distinct, ite_eq_left hb])
      (card_pair _ _ blk.distinct)
  · rw [hp]
    have hne : act D S x ≠ ∅ := by
      rw [← hact]
      exact Finset.nonempty_iff_ne_empty.mp ⟨blk.first, by simp [Nd3Block.activeLabels]⟩
    change (sidePartition (nd3Resolution (D.vertexPartition A) _ _
      (S.right q (S.edge (blk.singletonLabel q)))) side).Rel x y ↔ _
    rw [W4TargetPairings.FourStar.right_edge, eff_of_ne hne, ← hact, (ns_nd3 blk q).1,
      (ns_nd3 blk q).2]
    exact nd3_side_rel _ _ _ x y _ side

theorem new_rel_iff (hNoGlue : DanglingEdgeNoGlue D) (x y : Fin d) :
    (wholeResolution D S I.activeProfile.blockPattern q).newEdge.Rel x y ↔
      NewShape D S q x y := by
  rw [W4OutgoingSurvival.wholeResolution_newEdge_rel]
  have hax : (D.vertexPartition A).Rel ((D.vertexPartition A).repr x) x :=
    (D.vertexPartition A).rel_repr_left x
  unfold blockwiseResolution NewShape
  rcases pattern_cases D S I x with ⟨hp, hact⟩ | ⟨blk, hp, hact⟩ | ⟨blk, hp, hact⟩
  · rw [hp]
    change (nd2Resolution (D.vertexPartition A) _ (S.right q (S.edge 0))
      (S.right q (S.edge 1))).newEdge.Rel x y ↔ _
    rw [W4TargetPairings.FourStar.right_edge, W4TargetPairings.FourStar.right_edge, hact,
      eff_empty, ns_pair 0 1 (by decide)]
    exact nd2_new_rel _ hax y _ _ _ fun _ _ ↦
      inactive_rel_iff D S hNoGlue (by rw [hact]; exact Finset.notMem_empty _)
  · rw [hp]
    have hne : act D S x ≠ ∅ := by
      rw [← hact]
      exact Finset.nonempty_iff_ne_empty.mp ⟨blk.first, by simp [Nd2Block.activeLabels]⟩
    change (nd2Resolution (D.vertexPartition A) _ (S.right q (S.edge blk.first))
      (S.right q (S.edge blk.second))).newEdge.Rel x y ↔ _
    rw [W4TargetPairings.FourStar.right_edge, W4TargetPairings.FourStar.right_edge, eff_of_ne hne,
      ← hact]
    change _ ↔ _ ∧ (ns {blk.first, blk.second} q ≠ none → _)
    rw [ns_pair _ _ blk.distinct]
    refine nd2_new_rel _ hax y _ _ _ fun hb _ ↦ inactive_rel_iff D S hNoGlue ?_
    rw [← hact]
    exact ref_not_mem_of_card_two _ q _ (by change ns {blk.first, blk.second} q = _; rw [ns_pair _ _ blk.distinct, ite_eq_left hb])
      (card_pair _ _ blk.distinct)
  · rw [hp]
    have hne : act D S x ≠ ∅ := by
      rw [← hact]
      exact Finset.nonempty_iff_ne_empty.mp ⟨blk.first, by simp [Nd3Block.activeLabels]⟩
    change (nd3Resolution (D.vertexPartition A) _ _
      (S.right q (S.edge (blk.singletonLabel q)))).newEdge.Rel x y ↔ _
    rw [W4TargetPairings.FourStar.right_edge, eff_of_ne hne, ← hact, (ns_nd3 blk q).1,
      (ns_nd3 blk q).2]
    exact nd3_new_rel _ _ _ x y _

end Shape

/-! ## 5.  Naturality of the W4 shapes along a limit isomorphism -/

section Naturality

open DraismaVargas.Infrastructure W4StableSource W4Assembly

variable {Tm Tw : CFGraph} {d : ℕ} {Dm : GluingDatum Tm d} {Dw : GluingDatum Tw d}

theorem incident_star {T : CFGraph} {A : T.V} (S : W4TargetPairings.FourStar T A) (L : Fin 4) :
    ((S.edge L : T.edges) : T.V × T.V).1 = A ∨ ((S.edge L : T.edges) : T.V × T.V).2 = A := by
  have h := S.edge_mem_incidentEdges L
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem sourceEdgeEquiv_sourceEdge (φ : GeometricDatumIso Dm Dw) (e : Tm.edges) (s : Fin d) :
    φ.sourceEdgeEquiv (Dm.sourceEdge e s) = Dw.sourceEdge (φ.targetEdge e) (φ.edgePerm e s) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change φ.edgePerm e ((Dm.edgePartition e).repr s) =
    (Dw.edgePartition (φ.targetEdge e)).repr (φ.edgePerm e s)
  rw [φ.edgePartition e]
  change _ = φ.edgePerm e ((Dm.edgePartition e).repr ((φ.edgePerm e).symm (φ.edgePerm e s)))
  rw [Equiv.symm_apply_apply]

theorem vertexPerm_rel_iff (φ : GeometricDatumIso Dm Dw) (v : Tm.V) (a b : Fin d) :
    (Dw.vertexPartition (φ.targetVertex v)).Rel (φ.vertexPerm v a) (φ.vertexPerm v b) ↔
      (Dm.vertexPartition v).Rel a b := by
  rw [φ.vertexPartition v]
  exact (Dm.vertexPartition v).relabel_rel_iff _ a b

theorem edgePerm_rel_iff (φ : GeometricDatumIso Dm Dw) (e : Tm.edges) (a b : Fin d) :
    (Dw.edgePartition (φ.targetEdge e)).Rel (φ.edgePerm e a) (φ.edgePerm e b) ↔
      (Dm.edgePartition e).Rel a b := by
  rw [φ.edgePartition e]
  exact (Dm.edgePartition e).relabel_rel_iff _ a b

theorem edgePerm_rel_vertexPerm (φ : GeometricDatumIso Dm Dw) (e : Tm.edges) (v : Tm.V)
    (hv : (e : Tm.V × Tm.V).1 = v ∨ (e : Tm.V × Tm.V).2 = v) (s : Fin d) :
    (Dw.vertexPartition (φ.targetVertex v)).Rel (φ.edgePerm e s) (φ.vertexPerm v s) := by
  have h := φ.compatible e v hv s
  rw [← vertexPerm_rel_iff φ v, Equiv.apply_symm_apply] at h
  exact h

variable {Am : Tm.V} {Aw : Tw.V} (Sm : W4TargetPairings.FourStar Tm Am)
  (Sw : W4TargetPairings.FourStar Tw Aw) (φ : GeometricDatumIso Dm Dw)
  (hA : φ.targetVertex Am = Aw) (hS : ∀ L, φ.targetEdge (Sm.edge L) = Sw.edge L)
  (hConn : Dm.Connected)

include hA hS hConn in
theorem act_le (a : Fin d) (b : Fin d)
    (hb : (Dw.vertexPartition Aw).Rel b (φ.vertexPerm Am a)) (L : Fin 4)
    (hL : L ∈ act Dm Sm a) : L ∈ act Dw Sw b := by
  unfold act at hL ⊢
  rw [mem_activeLabels_iff] at hL ⊢
  obtain ⟨s, hs, hSurv⟩ := hL
  refine ⟨φ.edgePerm (Sm.edge L) s, ?_, ?_⟩
  · have h1 : (Dw.vertexPartition Aw).Rel (φ.vertexPerm Am a) (φ.vertexPerm Am s) := by
      rw [← hA, vertexPerm_rel_iff]
      exact ((Dm.vertexPartition Am).rel_repr_left a).symm.trans hs
    have h2 : (Dw.vertexPartition Aw).Rel (φ.edgePerm (Sm.edge L) s) (φ.vertexPerm Am s) := by
      rw [← hA]
      exact edgePerm_rel_vertexPerm φ _ Am (incident_star Sm L) s
    exact ((Dw.vertexPartition Aw).rel_repr_left b).trans (hb.trans (h1.trans h2.symm))
  · rw [← hS, ← sourceEdgeEquiv_sourceEdge, φ.isDangling_map_iff hConn]
    exact hSurv

theorem symm_targetVertex (hA' : φ.targetVertex Am = Aw) : φ.symm.targetVertex Aw = Am := by
  change φ.targetVertex.symm Aw = Am
  rw [← hA']
  exact φ.targetVertex.symm_apply_apply Am

include hA hS hConn in
/-- **Active labels are an isomorphism invariant.** -/
theorem act_map (a : Fin d) (b : Fin d)
    (hb : (Dw.vertexPartition Aw).Rel b (φ.vertexPerm Am a)) :
    act Dw Sw b = act Dm Sm a := by
  ext L
  constructor
  · intro hL
    have hA' : φ.symm.targetVertex Aw = Am := symm_targetVertex φ hA
    have hS' : ∀ L, φ.symm.targetEdge (Sw.edge L) = Sm.edge L := by
      intro L
      change φ.targetEdge.symm (Sw.edge L) = Sm.edge L
      rw [← hS]
      exact φ.targetEdge.symm_apply_apply _
    refine act_le Sw Sm φ.symm hA' hS' (φ.connected hConn) b a ?_ L hL
    change (Dm.vertexPartition Am).Rel a ((φ.vertexPerm (φ.targetVertex.symm Aw)).symm b)
    have hsymm : φ.targetVertex.symm Aw = Am := hA'
    rw [hsymm]
    rw [← vertexPerm_rel_iff φ Am, Equiv.apply_symm_apply, hA]
    exact hb.symm
  · exact act_le Sm Sw φ hA hS hConn a b hb L

theorem act_eq_of_rel {T : CFGraph} {A : T.V} (D : GluingDatum T d)
    (S : W4TargetPairings.FourStar T A) {a b : Fin d} (h : (D.vertexPartition A).Rel a b) :
    act D S a = act D S b := by
  unfold act
  congr 1
  exact Subtype.ext h

include hA hS hConn in
/-- **The side shapes are natural** along a limit isomorphism, for any sheet map that
agrees with the wall permutation modulo the wall partition and with the reference
occurrence's permutation on the blocks where the side is not joined. -/
theorem sideShape_map (q : Fin 3) (side : Bool) (τ : Fin d → Fin d)
    (hτ : ∀ a, (Dw.vertexPartition Aw).Rel (τ a) (φ.vertexPerm Am a))
    (hτE : ∀ a, ns (eff (act Dm Sm a)) q = some side →
      τ a = φ.edgePerm (Sm.edge (ref (eff (act Dm Sm a)) q)) a)
    (a b : Fin d) :
    SideShape Dm Sm q side a b ↔ SideShape Dw Sw q side (τ a) (τ b) := by
  unfold SideShape
  rw [act_map Sm Sw φ hA hS hConn a (τ a) (hτ a)]
  have hW : (Dw.vertexPartition Aw).Rel (τ a) (τ b) ↔ (Dm.vertexPartition Am).Rel a b := by
    rw [← vertexPerm_rel_iff φ Am, hA]
    exact ⟨fun h ↦ ((hτ a).symm.trans h).trans (hτ b),
      fun h ↦ ((hτ a).trans h).trans (hτ b).symm⟩
  constructor
  · rintro ⟨hab, himp⟩
    refine ⟨hW.mpr hab, fun hns ↦ ?_⟩
    have hbns : ns (eff (act Dm Sm b)) q = some side := by
      rwa [← act_eq_of_rel Dm Sm hab]
    rw [hτE a hns, hτE b hbns, ← act_eq_of_rel Dm Sm hab, ← hS, edgePerm_rel_iff]
    exact himp hns
  · rintro ⟨hab, himp⟩
    have hab' := hW.mp hab
    refine ⟨hab', fun hns ↦ ?_⟩
    have hbns : ns (eff (act Dm Sm b)) q = some side := by
      rwa [← act_eq_of_rel Dm Sm hab']
    have h := himp hns
    rw [hτE a hns, hτE b hbns, ← act_eq_of_rel Dm Sm hab', ← hS, edgePerm_rel_iff] at h
    exact h

include hA hS hConn in
/-- **The new-edge shapes are natural.** -/
theorem newShape_map (q : Fin 3) (τ : Fin d → Fin d)
    (hτ : ∀ a, (Dw.vertexPartition Aw).Rel (τ a) (φ.vertexPerm Am a))
    (hτE : ∀ a, ns (eff (act Dm Sm a)) q ≠ none →
      τ a = φ.edgePerm (Sm.edge (ref (eff (act Dm Sm a)) q)) a)
    (a b : Fin d) :
    NewShape Dm Sm q a b ↔ NewShape Dw Sw q (τ a) (τ b) := by
  unfold NewShape
  rw [act_map Sm Sw φ hA hS hConn a (τ a) (hτ a)]
  have hW : (Dw.vertexPartition Aw).Rel (τ a) (τ b) ↔ (Dm.vertexPartition Am).Rel a b := by
    rw [← vertexPerm_rel_iff φ Am, hA]
    exact ⟨fun h ↦ ((hτ a).symm.trans h).trans (hτ b),
      fun h ↦ ((hτ a).trans h).trans (hτ b).symm⟩
  constructor
  · rintro ⟨hab, himp⟩
    refine ⟨hW.mpr hab, fun hns ↦ ?_⟩
    have hbns : ns (eff (act Dm Sm b)) q ≠ none := by
      rwa [← act_eq_of_rel Dm Sm hab]
    rw [hτE a hns, hτE b hbns, ← act_eq_of_rel Dm Sm hab, ← hS, edgePerm_rel_iff]
    exact himp hns
  · rintro ⟨hab, himp⟩
    have hab' := hW.mp hab
    refine ⟨hab', fun hns ↦ ?_⟩
    have hbns : ns (eff (act Dm Sm b)) q ≠ none := by
      rwa [← act_eq_of_rel Dm Sm hab']
    have h := himp hns
    rw [hτE a hns, hτE b hbns, ← act_eq_of_rel Dm Sm hab', ← hS, edgePerm_rel_iff] at h
    exact h

end Naturality

section Perms

open DraismaVargas.Infrastructure W4StableSource W4Assembly

variable {Tm Tw : CFGraph} {d : ℕ} {Dm : GluingDatum Tm d} {Dw : GluingDatum Tw d}
  {Am : Tm.V} {Aw : Tw.V} (Sm : W4TargetPairings.FourStar Tm Am)
  (φ : GeometricDatumIso Dm Dw) (hA : φ.targetVertex Am = Aw)

include hA in
/-- A sheet map agreeing with the wall permutation modulo the wall partition and
injective on each wall block is injective. -/
theorem injective_of_blockwise (τ : Fin d → Fin d)
    (hτ : ∀ a, (Dw.vertexPartition Aw).Rel (τ a) (φ.vertexPerm Am a))
    (hBlock : ∀ a b, (Dm.vertexPartition Am).Rel a b → τ a = τ b → a = b) :
    Function.Injective τ := by
  intro a b hab
  apply hBlock a b _ hab
  rw [← vertexPerm_rel_iff φ Am, hA]
  have hb := hτ b
  rw [← hab] at hb
  exact (hτ a).symm.trans hb

/-- The side permutation: the reference occurrence's permutation on the blocks where the
side is not joined, the wall permutation elsewhere. -/
noncomputable def sideFun (q : Fin 3) (side : Bool) (a : Fin d) : Fin d :=
  if ns (eff (act Dm Sm a)) q = some side then
    φ.edgePerm (Sm.edge (ref (eff (act Dm Sm a)) q)) a
  else φ.vertexPerm Am a

/-- The new-edge permutation. -/
noncomputable def newFun (q : Fin 3) (a : Fin d) : Fin d :=
  if ns (eff (act Dm Sm a)) q ≠ none then
    φ.edgePerm (Sm.edge (ref (eff (act Dm Sm a)) q)) a
  else φ.vertexPerm Am a

include hA in
theorem sideFun_rel (q : Fin 3) (side : Bool) (a : Fin d) :
    (Dw.vertexPartition Aw).Rel (sideFun Sm φ q side a) (φ.vertexPerm Am a) := by
  unfold sideFun
  split_ifs
  · rw [← hA]
    exact edgePerm_rel_vertexPerm φ _ Am (incident_star Sm _) a
  · rfl

include hA in
theorem newFun_rel (q : Fin 3) (a : Fin d) :
    (Dw.vertexPartition Aw).Rel (newFun Sm φ q a) (φ.vertexPerm Am a) := by
  unfold newFun
  split_ifs
  · rw [← hA]
    exact edgePerm_rel_vertexPerm φ _ Am (incident_star Sm _) a
  · rfl

include hA in
theorem sideFun_injective (q : Fin 3) (side : Bool) : Function.Injective (sideFun Sm φ q side) := by
  refine injective_of_blockwise φ hA _ (sideFun_rel Sm φ hA q side) fun a b hab h ↦ ?_
  unfold sideFun at h
  rw [act_eq_of_rel Dm Sm hab] at h
  split_ifs at h
  · exact (φ.edgePerm _).injective h
  · exact (φ.vertexPerm Am).injective h

include hA in
theorem newFun_injective (q : Fin 3) : Function.Injective (newFun Sm φ q) := by
  refine injective_of_blockwise φ hA _ (newFun_rel Sm φ hA q) fun a b hab h ↦ ?_
  unfold newFun at h
  rw [act_eq_of_rel Dm Sm hab] at h
  split_ifs at h
  · exact (φ.edgePerm _).injective h
  · exact (φ.vertexPerm Am).injective h

noncomputable def sidePerm (q : Fin 3) (side : Bool) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (sideFun Sm φ q side)
    (Finite.injective_iff_bijective.mp (sideFun_injective Sm φ hA q side))

noncomputable def newPerm (q : Fin 3) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (newFun Sm φ q) (Finite.injective_iff_bijective.mp (newFun_injective Sm φ hA q))

theorem sidePerm_apply (q : Fin 3) (side : Bool) (a : Fin d) :
    sidePerm Sm φ hA q side a = sideFun Sm φ q side a := rfl

theorem newPerm_apply (q : Fin 3) (a : Fin d) : newPerm Sm φ hA q a = newFun Sm φ q a := rfl

end Perms

/-! ## 6.  A coherent limit isomorphism carries a W4 family resolution onto the wall's -/

section Transport

open DraismaVargas.Infrastructure W4StableSource W4Assembly ResolutionM11
open W4OutgoingSurvival (sidePartition)

variable {Tm Tw : CFGraph} {d : ℕ} {Dm : GluingDatum Tm d} {Dw : GluingDatum Tw d}
  {Am : Tm.V} {Aw : Tw.V} (Sm : W4TargetPairings.FourStar Tm Am)
  (Sw : W4TargetPairings.FourStar Tw Aw) (φ : GeometricDatumIso Dm Dw)
  (hA : φ.targetVertex Am = Aw) (hS : ∀ L, φ.targetEdge (Sm.edge L) = Sw.edge L)
  (hConn : Dm.Connected) (Im : AuxR0SourceInput Dm Sm) (Iw : AuxR0SourceInput Dw Sw) (q : Fin 3)

/-- **Coherence**: on every block whose resolution is not joined on a side, every star
occurrence placed on that side carries the reference occurrence's permutation. -/
def Coherent : Prop :=
  ∀ (s : Fin d) (L : Fin 4), ns (eff (act Dm Sm s)) q = some (labelRight q L) →
    φ.edgePerm (Sm.edge L) s = φ.edgePerm (Sm.edge (ref (eff (act Dm Sm s)) q)) s

theorem sidePartition_rel_iff (r : LocalResolution d) (side : Bool) (a b : Fin d) :
    (sidePartition r side).Rel a b ↔ (if side then r.right else r.left).Rel a b := by
  cases side <;> rfl

include hA hS hConn in
/-- **The coherent transport.**  A member resolution with the blocks of its own W4 family
at the pairing `q` is carried onto the wall's family at `q` by a decoupled transport along
any coherent limit isomorphism. -/
theorem nonempty_transportFree_of_coherent (res : LocalResolution d)
    (hresL : res.left.SameBlocks (wholeResolution Dm Sm Im.activeProfile.blockPattern q).left)
    (hresR : res.right.SameBlocks (wholeResolution Dm Sm Im.activeProfile.blockPattern q).right)
    (hresN : res.newEdge.SameBlocks
      (wholeResolution Dm Sm Im.activeProfile.blockPattern q).newEdge)
    (right : Tm.edges → Bool) (hSide : ∀ e, Sw.right q (φ.targetEdge e) = right e)
    (hCoh : Coherent Sm φ q) :
    Nonempty (ResolutionExpansionFree.TransportFree φ Am Aw right (Sw.right q) res
      (wholeResolution Dw Sw Iw.activeProfile.blockPattern q)) := by
  have hNGm := Im.dangling_no_glue
  have hNGw := Iw.dangling_no_glue
  set τO := sidePerm Sm φ hA q false
  set τF := sidePerm Sm φ hA q true
  set τN := newPerm Sm φ hA q
  -- the member's three partitions, as shapes
  have hMs : ∀ side a b, (sidePartition res side).Rel a b ↔ SideShape Dm Sm q side a b := by
    intro side a b
    rw [← side_rel_iff Dm Sm Im q hNGm side a b]
    cases side
    · exact hresL a b
    · exact hresR a b
  have hMn : ∀ a b, res.newEdge.Rel a b ↔ NewShape Dm Sm q a b := fun a b ↦
    (hresN a b).trans (new_rel_iff Dm Sm Im q hNGm a b)
  have hWs : ∀ side a b, (sidePartition (wholeResolution Dw Sw Iw.activeProfile.blockPattern q)
      side).Rel a b ↔ SideShape Dw Sw q side a b := fun side a b ↦
    side_rel_iff Dw Sw Iw q hNGw side a b
  have hSideMap : ∀ side a b, SideShape Dm Sm q side a b ↔
      SideShape Dw Sw q side (sidePerm Sm φ hA q side a) (sidePerm Sm φ hA q side b) :=
    fun side a b ↦ sideShape_map Sm Sw φ hA hS hConn q side (sidePerm Sm φ hA q side)
      (sideFun_rel Sm φ hA q side) (fun a h ↦ by
        change sideFun Sm φ q side a = _
        unfold sideFun
        rw [ite_eq_left h]) a b
  have hNewMap : ∀ a b, NewShape Dm Sm q a b ↔ NewShape Dw Sw q (τN a) (τN b) :=
    fun a b ↦ newShape_map Sm Sw φ hA hS hConn q τN (newFun_rel Sm φ hA q) (fun a h ↦ by
        change newFun Sm φ q a = _
        unfold newFun
        rw [ite_eq_left h]) a b
  -- agreement with the wall permutation, pulled back
  have hAgree : ∀ (τ : Equiv.Perm (Fin d)),
      (∀ a, (Dw.vertexPartition Aw).Rel (τ a) (φ.vertexPerm Am a)) →
      ∀ s, (Dm.vertexPartition Am).Rel ((φ.vertexPerm Am).symm (τ s)) s := by
    intro τ hτ s
    rw [← vertexPerm_rel_iff φ Am, Equiv.apply_symm_apply, hA]
    exact hτ s
  have hBack : ∀ (τ : Equiv.Perm (Fin d)),
      (∀ a, (Dw.vertexPartition Aw).Rel (τ a) (φ.vertexPerm Am a)) →
      ∀ s t, (Dw.vertexPartition Aw).Rel t (φ.vertexPerm Am s) →
        (Dm.vertexPartition Am).Rel (τ.symm t) s := by
    intro τ hτ s t ht
    rw [← vertexPerm_rel_iff φ Am, hA]
    have h := hτ (τ.symm t)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans ht
  have hRefines : ∀ side, (sidePartition res side).Refines (Dm.vertexPartition Am) := by
    intro side a b h
    exact ((hMs side a b).mp h).1
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel φ Am Aw right (Sw.right q) res _
    hA hSide (hRefines false) (hRefines true) τO τF τN
    (hAgree τO (sideFun_rel Sm φ hA q false)) (hAgree τF (sideFun_rel Sm φ hA q true))
    (fun a b ↦ ((hMs false a b).trans (hSideMap false a b)).trans (hWs false _ _).symm)
    (fun a b ↦ ((hMs true a b).trans (hSideMap true a b)).trans (hWs true _ _).symm)
    (fun a b ↦ ((hMn a b).trans (hNewMap a b)).trans
      (new_rel_iff Dw Sw Iw q hNGw _ _).symm) ?_ ?_ ?_
  · -- the regrown occurrence against the retained endpoint
    intro s
    have hrel : (Dm.vertexPartition Am).Rel (τO.symm (τN s)) s :=
      hBack τO (sideFun_rel Sm φ hA q false) s (τN s) (newFun_rel Sm φ hA q s)
    refine (hMs false _ s).mpr ⟨hrel, fun hns ↦ ?_⟩
    have hEq : τN s = τO s := by
      change newFun Sm φ q s = sideFun Sm φ q false s
      have hns' : ns (eff (act Dm Sm s)) q = some false := by
        rwa [act_eq_of_rel Dm Sm hrel] at hns
      unfold newFun sideFun
      rw [ite_eq_left (by rw [hns']; exact Option.some_ne_none _), ite_eq_left hns']
    rw [hEq, Equiv.symm_apply_apply]
    rfl
  · intro s
    have hrel : (Dm.vertexPartition Am).Rel (τF.symm (τN s)) s :=
      hBack τF (sideFun_rel Sm φ hA q true) s (τN s) (newFun_rel Sm φ hA q s)
    refine (hMs true _ s).mpr ⟨hrel, fun hns ↦ ?_⟩
    have hEq : τN s = τF s := by
      change newFun Sm φ q s = sideFun Sm φ q true s
      have hns' : ns (eff (act Dm Sm s)) q = some true := by
        rwa [act_eq_of_rel Dm Sm hrel] at hns
      unfold newFun sideFun
      rw [ite_eq_left (by rw [hns']; exact Option.some_ne_none _), ite_eq_left hns']
    rw [hEq, Equiv.symm_apply_apply]
    rfl
  · -- the endpoint compatibility, from coherence
    intro e hInc s
    obtain ⟨L, rfl⟩ := Sm.exists_edge_eq e (by
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hInc)
    have hRight : right (Sm.edge L) = labelRight q L := by
      rw [← hSide, hS, W4TargetPairings.FourStar.right_edge]
    rw [hRight]
    set side := labelRight q L with hside
    have hGoal : (sidePartition res side).Rel ((sidePerm Sm φ hA q side).symm
        (φ.edgePerm (Sm.edge L) s)) s := by
      have hCompat : (Dw.vertexPartition Aw).Rel (φ.edgePerm (Sm.edge L) s) (φ.vertexPerm Am s) := by
        rw [← hA]
        exact edgePerm_rel_vertexPerm φ _ Am (incident_star Sm L) s
      have hrel : (Dm.vertexPartition Am).Rel ((sidePerm Sm φ hA q side).symm
          (φ.edgePerm (Sm.edge L) s)) s :=
        hBack _ (sideFun_rel Sm φ hA q side) s _ hCompat
      refine (hMs side _ s).mpr ⟨hrel, fun hns ↦ ?_⟩
      have hns' : ns (eff (act Dm Sm s)) q = some side := by
        rwa [act_eq_of_rel Dm Sm hrel] at hns
      have hEq : φ.edgePerm (Sm.edge L) s = sidePerm Sm φ hA q side s := by
        change _ = sideFun Sm φ q side s
        unfold sideFun
        rw [ite_eq_left hns']
        exact hCoh s L hns'
      rw [hEq, Equiv.symm_apply_apply]
      rfl
    cases hside' : side
    · rw [hside'] at hGoal
      simpa using hGoal
    · rw [hside'] at hGoal
      simpa using hGoal

end Transport

/-! ## 7.  The facts the pendant construction consumes, at a regrowth's limit -/

section LimitFacts

open GluingContraction GraphContraction TargetExpansion
open W4TargetPairings (FourStar)
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))

/-- Every vertex of a regrowth's limit other than the merge is change-minimal. -/
theorem limit_changeMinimalAt (X : (w.frame.limitTarget w.column).V) (hX : X ≠ mergeVertex w) :
    w.limit.ChangeMinimalAt X := by
  by_contra h
  exact hX (MergePinning.eq_merge_of_targetExcess_ne_zero w.frame.data
    w.frame.fullDim.changeMinimal rfl (fst_ne_snd _) (w.frame.numEdges_edgeOf w.column) X h)

include hy star in
/-- A four-valent regrowth's limit has no entirely dangling target fibre: its own
full-dimensional family member (`RegrowthWallInput.w4Matched`) has none, and retained
occurrences dangle in the member exactly when they dangle in the limit. -/
theorem limit_noDanglingTargetFibres : NoDanglingTargetFibres w.limit := by
  classical
  intro f
  let c := W4OutgoingStableRows.member (RegrowthWallInput.w4Input w hy star)
    (RegrowthWallInput.w4Incoming w star)
  obtain ⟨g, hg, hgnd⟩ := (RegrowthWallInput.w4Matched w hy star).noDanglingTargetFibres
    (occurrenceEquiv _ (mergeVertex w) c.right (some f))
  rcases ResolutionPruning.sourceEdge_cases c g with ⟨old, rfl⟩ | ⟨sheet, rfl⟩
  · refine ⟨old, ?_, fun hd ↦ hgnd ((ResolutionPruning.isDangling_oldSourceEdge_iff c
      (RegrowthWallInput.w4Input w hy star).valid
      (W4OutgoingStableRows.member_sourceGenus _ _) old).mpr hd)⟩
    exact Option.some.inj ((occurrenceEquiv _ (mergeVertex w) c.right).injective hg)
  · exact absurd ((occurrenceEquiv _ (mergeVertex w) c.right).injective hg) (by simp)

end LimitFacts

/-! ## 8.  Pendant limit automorphisms of a four-valent wall -/

section PendantLimit

open GluingContraction GraphContraction TargetExpansion TargetSeparation
open W4TargetPairings (FourStar)
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w)) (K : Fin 4)
  (σ : Equiv.Perm (Fin degree))
  (hInner : ∀ s, (w.limit.vertexPartition (mergeVertex w)).Rel (σ s) s)
  (M : Fin degree → Prop)
  (hM : ∀ s, M s → IsDangling w.limit (w.limit.sourceEdge (star.edge K) s) ∧
    ∃ g : w.limit.SourceEdge, ¬ IsDangling w.limit g ∧
      Incident w.limit g (w.limit.sourceEndpoint (mergeVertex w) s))
  (hMoved : ∀ s, σ s ≠ s → M s)

/-- The pendant automorphism of the wall's limit on the branch of `star.edge K`. -/
noncomputable def pendantDatum : GeometricDatumIso w.limit w.limit :=
  pendantIso w.limit (mergeVertex w) (farEndpoint (mergeVertex w) (star.edge K))
    (farEndpoint_ne (incident_star star K)) σ hInner
    (fun s hs _X hX t hst ↦ pendant_single w.limit (incident_star star K)
      (RegrowthWallInput.w4Input w hy star).valid (RegrowthWallInput.w4Input w hy star).dangling_no_glue
      (limit_noDanglingTargetFibres w hy star) (W4StarParity.limitTarget_connected w)
      (limit_changeMinimalAt w) M hM s (hMoved s hs) hX t hst)

/-- **The pendant automorphism as a labelled limit isomorphism**: it fixes every branch
vertex and every stable path, since it moves only pendant sheets. -/
noncomputable def pendantLimitIso : GeometricStar.LimitIso hy w w where
  datum := pendantDatum w hy star K σ hInner M hM hMoved
  overCore_vertex b := congrArg (InheritedLimitIncidence.coreIdentification w hy).vertex
    (pendantIso_branch w.limit (mergeVertex w) (farEndpoint (mergeVertex w) (star.edge K))
      (farEndpoint_ne (incident_star star K)) σ hInner _
      (fun s hs _X hX ↦ pendant_zero w.limit (incident_star star K) M hM s (hMoved s hs) hX)
      (InheritedLimitRows.limit_connected w) b)
  overCore_row r := congrArg (InheritedLimitIncidence.coreIdentification w hy).row
    (pendantIso_row w.limit (mergeVertex w) (farEndpoint (mergeVertex w) (star.edge K))
      (farEndpoint_ne (incident_star star K)) σ hInner _
      (fun g hg hs ↦ pendant_edge_isDangling w.limit (incident_star star K) M hM g hg (hMoved _ hs))
      (InheritedLimitRows.limit_connected w) r)

theorem pendantLimitIso_vertexPerm (X : (w.frame.limitTarget w.column).V) :
    (pendantLimitIso w hy star K σ hInner M hM hMoved).datum.vertexPerm X =
      GluingDatum.SheetRelabeling.togglePermutation
        (TargetBranchRegion.vertexMoved (mergeVertex w) (farEndpoint (mergeVertex w) (star.edge K))
          (farEndpoint_ne (incident_star star K)) X) σ := rfl

theorem pendantLimitIso_edgePerm (f : (w.frame.limitTarget w.column).edges) :
    (pendantLimitIso w hy star K σ hInner M hM hMoved).datum.edgePerm f =
      GluingDatum.SheetRelabeling.togglePermutation
        (TargetBranchRegion.edgeMoved (mergeVertex w) (farEndpoint (mergeVertex w) (star.edge K))
          (farEndpoint_ne (incident_star star K)) f) σ := rfl

theorem pendantLimitIso_targetVertex :
    (pendantLimitIso w hy star K σ hInner M hM hMoved).datum.targetVertex = Equiv.refl _ := rfl

theorem pendantLimitIso_targetEdge :
    (pendantLimitIso w hy star K σ hInner M hM hMoved).datum.targetEdge = Equiv.refl _ := rfl

end PendantLimit

/-! ## 9.  Dangling wall blocks are single sheets -/

section DanglingBlock

open GluingContraction W4StableSource W4Assembly
open W4TargetPairings (FourStar)

variable {T : CFGraph} {d : ℕ} {A : T.V} (D : GluingDatum T d) (S : FourStar T A)
  (I : AuxR0SourceInput D S)

include I in
/-- **An entirely dangling wall block is a single sheet**: it carries no surviving
occurrence, and Equation (C) at a four-valent wall leaves it no ramification. -/
theorem eq_of_act_empty {t u : Fin d} (hAct : act D S t = ∅) (htu : (D.vertexPartition A).Rel t u) :
    t = u := by
  classical
  set v := D.sourceEndpoint A t
  have hZeroVal : nonDanglingValency D v = 0 := by
    rw [← card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro g _ hSurv
    obtain ⟨g, hg⟩ := g
    apply hSurv
    have hEnd : (g.1.1 : T.V × T.V).1 = A ∧ (D.vertexPartition A).Rel g.1.2 t ∨
        (g.1.1 : T.V × T.V).2 = A ∧ (D.vertexPartition A).Rel g.1.2 t := by
      rcases hg with h | h
      · obtain ⟨h1, h2⟩ := (D.sourceEndpoint_eq_iff _ _ _).mp h
        have hA' : (g.1.1 : T.V × T.V).1 = A := h1
        rw [hA'] at h2
        exact Or.inl ⟨hA', h2.trans ((D.vertexPartition A).rel_repr_left t)⟩
      · obtain ⟨h1, h2⟩ := (D.sourceEndpoint_eq_iff _ _ _).mp h
        have hA' : (g.1.1 : T.V × T.V).2 = A := h1
        rw [hA'] at h2
        exact Or.inr ⟨hA', h2.trans ((D.vertexPartition A).rel_repr_left t)⟩
    have hInc : g.1.1 ∈ GluingDatum.incidentEdges A := by
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hEnd with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    obtain ⟨K, hK⟩ := S.exists_edge_eq g.1.1 hInc
    have hgEq : g = D.sourceEdge (S.edge K) g.1.2 := by
      apply Subtype.ext
      rw [hK]
      exact Prod.ext rfl g.2.symm
    change IsDangling D g
    rw [hgEq]
    have hRel : (D.vertexPartition A).Rel (WallBlock.ofSheet D A t).1 g.1.2 := by
      change (D.vertexPartition A).Rel ((D.vertexPartition A).repr t) g.1.2
      rcases hEnd with h | h
      · exact ((D.vertexPartition A).rel_repr_left t).trans h.2.symm
      · exact ((D.vertexPartition A).rel_repr_left t).trans h.2.symm
    refine isDangling_sourceEdge_of_not_mem_activeLabels D S _ K ?_ g.1.2 hRel
    change K ∉ act D S t
    rw [hAct]
    exact Finset.notMem_empty K
  have hZeroRam : D.localRamification v.1.1 ⟨v.1.2, v.2⟩ = 0 := by
    have hSum := AuxR0SourceInput.targetChange_eq_zero I
    unfold GluingDatum.targetChange at hSum
    have hNonneg : ∀ b ∈ (Finset.univ : Finset (D.vertexPartition A).Blocks),
        0 ≤ D.localRamification A b := fun b _ ↦
      D.localRamification_nonneg A (I.valid.2 A) b
    exact (Finset.sum_eq_zero_iff_of_nonneg hNonneg).mp hSum ⟨v.1.2, v.2⟩ (Finset.mem_univ _)
  have hOne := NonDanglingValency.blockCard_eq_one_of_nonDanglingValency_eq_zero D
    I.dangling_no_glue v hZeroRam
    hZeroVal
  have hBlock := (D.vertexPartition A).block_eq_singleton_of_blockCard_eq_one _ hOne
  have ht : t ∈ (D.vertexPartition A).block v.1.2 :=
    ((D.vertexPartition A).mem_block_iff _ _).mpr ((D.vertexPartition A).rel_repr_left t)
  have hu : u ∈ (D.vertexPartition A).block v.1.2 :=
    ((D.vertexPartition A).mem_block_iff _ _).mpr (((D.vertexPartition A).rel_repr_left t).trans htu)
  rw [hBlock, Finset.mem_singleton] at ht hu
  rw [ht, hu]

end DanglingBlock

/-! ## 10.  The member's read-off resolution has its own W4 family's blocks -/

section MemberShape

open GluingContraction GraphContraction TargetExpansion
open W4TargetPairings (FourStar)
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))
  (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

/-- The member's own W4 input, on its own limit with the inherited labels. -/
noncomputable abbrev memberInput :=
  RegrowthWallInput.w4Input other hy (W4WallExhaustion.inheritedStar other ψ hFour star)

/-- The member's own family receipts at its own pairing (Part I's incoming identification,
`W4IncomingPairingReceipts.receiptsOfForest`, with no discreteness). -/
theorem memberReceipts :
    GlobalW4.PairingReceipts other.limit (W4WallExhaustion.inheritedStar other ψ hFour star)
      (W4IncomingGlobalMatching.blockPattern other.frame.data rfl
        (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
        (W4WallExhaustion.inheritedStar other ψ hFour star)
        (memberInput w hy star hFour other ψ).blockPicture)
      (W4WallExhaustion.index hFour star other ψ) :=
  W4IncomingPairingReceipts.receiptsOfForest other.frame.data other.frame.fullDim rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (W4WallExhaustion.inheritedStar other ψ hFour star) (InheritedLimitRows.forest other hy)
    (InheritedLimitRows.danglingCompatible other hy) (memberInput w hy star hFour other ψ).blockPicture

theorem member_pattern_eq :
    W4IncomingGlobalMatching.blockPattern other.frame.data rfl
        (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
        (W4WallExhaustion.inheritedStar other ψ hFour star)
        (memberInput w hy star hFour other ψ).blockPicture =
      (memberInput w hy star hFour other ψ).activeProfile.blockPattern :=
  W4PositiveExit.blockPattern_eq _ rfl _ _ _ _

theorem iff_of_eq {d : ℕ} {P Q : SheetPartition d} (h : P = Q) (i j : Fin d) :
    P.Rel i j ↔ Q.Rel i j := h ▸ Iff.rfl

theorem member_left_sameBlocks :
    (W4NonDiscreteStarCensus.memberResolution w hy star hFour other ψ).left.SameBlocks
      (W4Assembly.wholeResolution other.limit (W4WallExhaustion.inheritedStar other ψ hFour star)
        (memberInput w hy star hFour other ψ).activeProfile.blockPattern
        (W4WallExhaustion.index hFour star other ψ)).left := by
  have h := W4IncomingRepresentatives.transported_sameBlocks_vertexPartition other.frame.data
    other.frame.fullDim rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (W4WallExhaustion.inheritedStar other ψ hFour star)
    (InheritedLimitRows.danglingCompatible other hy) (memberInput w hy star hFour other ψ).blockPicture
    (memberReceipts w hy star hFour other ψ) (oldVertex _ (mergeVertex other))
  have h2 := W4IncomingRepresentatives.candidate_datum_vertexPartition_old_wall other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (W4WallExhaustion.inheritedStar other ψ hFour star) _ _ (memberReceipts w hy star hFour other ψ)
  intro i j
  refine (h i j).trans ((iff_of_eq h2 i j).trans ?_)
  exact Eq.to_iff (congrArg (fun pat ↦ (W4Assembly.wholeResolution other.limit
    (W4WallExhaustion.inheritedStar other ψ hFour star) pat
    (W4WallExhaustion.index hFour star other ψ)).left.Rel i j) (member_pattern_eq w hy star hFour other ψ))

theorem member_right_sameBlocks :
    (W4NonDiscreteStarCensus.memberResolution w hy star hFour other ψ).right.SameBlocks
      (W4Assembly.wholeResolution other.limit (W4WallExhaustion.inheritedStar other ψ hFour star)
        (memberInput w hy star hFour other ψ).activeProfile.blockPattern
        (W4WallExhaustion.index hFour star other ψ)).right := by
  have h := W4IncomingRepresentatives.transported_sameBlocks_vertexPartition other.frame.data
    other.frame.fullDim rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (W4WallExhaustion.inheritedStar other ψ hFour star)
    (InheritedLimitRows.danglingCompatible other hy) (memberInput w hy star hFour other ψ).blockPicture
    (memberReceipts w hy star hFour other ψ) (freshVertex _)
  have h2 := W4IncomingRepresentatives.candidate_datum_vertexPartition_fresh other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (W4WallExhaustion.inheritedStar other ψ hFour star) _ _ (memberReceipts w hy star hFour other ψ)
  intro i j
  refine (h i j).trans ((iff_of_eq h2 i j).trans ?_)
  exact Eq.to_iff (congrArg (fun pat ↦ (W4Assembly.wholeResolution other.limit
    (W4WallExhaustion.inheritedStar other ψ hFour star) pat
    (W4WallExhaustion.index hFour star other ψ)).right.Rel i j) (member_pattern_eq w hy star hFour other ψ))

theorem member_newEdge_sameBlocks :
    (W4NonDiscreteStarCensus.memberResolution w hy star hFour other ψ).newEdge.SameBlocks
      (W4Assembly.wholeResolution other.limit (W4WallExhaustion.inheritedStar other ψ hFour star)
        (memberInput w hy star hFour other ψ).activeProfile.blockPattern
        (W4WallExhaustion.index hFour star other ψ)).newEdge := by
  have h := W4IncomingRepresentatives.transported_sameBlocks_edge_new other.frame.data
    other.frame.fullDim rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (W4WallExhaustion.inheritedStar other ψ hFour star)
    (InheritedLimitRows.danglingCompatible other hy) (memberInput w hy star hFour other ψ).blockPicture
    (memberReceipts w hy star hFour other ψ)
  have h2 := W4IncomingRepresentatives.candidate_datum_edgePartition_new other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (W4WallExhaustion.inheritedStar other ψ hFour star) _ _ (memberReceipts w hy star hFour other ψ)
  intro i j
  refine (h i j).trans ((iff_of_eq h2 i j).trans ?_)
  exact Eq.to_iff (congrArg (fun pat ↦ (W4Assembly.wholeResolution other.limit
    (W4WallExhaustion.inheritedStar other ψ hFour star) pat
    (W4WallExhaustion.index hFour star other ψ)).newEdge.Rel i j) (member_pattern_eq w hy star hFour other ψ))

end MemberShape

/-! ## 11.  Coherence by pendant relabelling -/

section Coherence

open GluingContraction GraphContraction TargetExpansion TargetSeparation
open W4TargetPairings (FourStar)
open W4StableSource FullDimensionalSource StableGraphIncidence W4Assembly
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))
  (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

/-- The wall sheets whose `K` occurrence must be re-pointed: those in a non-dangling block
whose non-joined side (at the member's pairing) carries `K` as a non-reference label. -/
def Adj (K : Fin 4) (t : Fin degree) : Prop :=
  act w.limit star t ≠ ∅ ∧
    ns (eff (act w.limit star t)) (W4WallExhaustion.index hFour star other ψ) =
      some (labelRight (W4WallExhaustion.index hFour star other ψ) K) ∧
    K ≠ ref (eff (act w.limit star t)) (W4WallExhaustion.index hFour star other ψ)

/-- The re-pointing permutation of the `K` pendant: on an adjusted sheet `t`, go back to
the member along `K`'s own permutation and forward along the reference label's. -/
noncomputable def adjFun (K : Fin 4) (t : Fin degree) : Fin degree := by
  classical
  exact if Adj w hy star hFour other ψ K t then
    ψ.datum.edgePerm ((W4WallExhaustion.inheritedStar other ψ hFour star).edge
        (ref (eff (act w.limit star t)) (W4WallExhaustion.index hFour star other ψ)))
      ((ψ.datum.edgePerm ((W4WallExhaustion.inheritedStar other ψ hFour star).edge K)).symm t)
  else t

include hFour in
theorem hAψ : ψ.datum.targetVertex (mergeVertex other) = mergeVertex w :=
  W4WallExhaustion.map_merge other ψ hFour

theorem hSψ (L : Fin 4) :
    ψ.datum.targetEdge ((W4WallExhaustion.inheritedStar other ψ hFour star).edge L) = star.edge L :=
  W4WallExhaustion.inheritedStar_edge other ψ hFour star L

/-- Every sheet permutation of the member at an occurrence of its star lands in the wall
block of the wall permutation. -/
theorem edgePerm_rel (L : Fin 4) (s : Fin degree) :
    (w.limit.vertexPartition (mergeVertex w)).Rel
      (ψ.datum.edgePerm ((W4WallExhaustion.inheritedStar other ψ hFour star).edge L) s)
      (ψ.datum.vertexPerm (mergeVertex other) s) := by
  rw [← hAψ w hy hFour other ψ]
  exact edgePerm_rel_vertexPerm ψ.datum _ _ (incident_star _ L) s

theorem adjFun_rel (K : Fin 4) (t : Fin degree) :
    (w.limit.vertexPartition (mergeVertex w)).Rel (adjFun w hy star hFour other ψ K t) t := by
  classical
  unfold adjFun
  split_ifs
  · set s := (ψ.datum.edgePerm ((W4WallExhaustion.inheritedStar other ψ hFour star).edge K)).symm t
    have ht : ψ.datum.edgePerm ((W4WallExhaustion.inheritedStar other ψ hFour star).edge K) s = t :=
      Equiv.apply_symm_apply _ t
    have h1 := edgePerm_rel w hy star hFour other ψ K s
    rw [ht] at h1
    exact (edgePerm_rel w hy star hFour other ψ _ s).trans h1.symm
  · rfl

theorem adjFun_injective (K : Fin 4) : Function.Injective (adjFun w hy star hFour other ψ K) := by
  classical
  intro t u htu
  have hRel : (w.limit.vertexPartition (mergeVertex w)).Rel t u := by
    have h2 := adjFun_rel w hy star hFour other ψ K u
    rw [← htu] at h2
    exact (adjFun_rel w hy star hFour other ψ K t).symm.trans h2
  unfold adjFun at htu
  have hAdj : Adj w hy star hFour other ψ K t ↔ Adj w hy star hFour other ψ K u := by
    unfold Adj
    rw [act_eq_of_rel w.limit star hRel]
  rw [act_eq_of_rel w.limit star hRel] at htu
  by_cases h : Adj w hy star hFour other ψ K u
  · rw [ite_eq_left (hAdj.mpr h), ite_eq_left h] at htu
    exact (Equiv.injective _) ((Equiv.injective _) htu)
  · rw [ite_eq_right (fun h' ↦ h (hAdj.mp h')), ite_eq_right h] at htu
    exact htu

/-- The re-pointing permutation. -/
noncomputable def adjPerm (K : Fin 4) : Equiv.Perm (Fin degree) :=
  Equiv.ofBijective (adjFun w hy star hFour other ψ K)
    (Finite.injective_iff_bijective.mp (adjFun_injective w hy star hFour other ψ K))

theorem adjPerm_apply (K : Fin 4) (t : Fin degree) :
    adjPerm w hy star hFour other ψ K t = adjFun w hy star hFour other ψ K t := rfl

theorem adjPerm_rel (K : Fin 4) (t : Fin degree) :
    (w.limit.vertexPartition (mergeVertex w)).Rel (adjPerm w hy star hFour other ψ K t) t :=
  adjFun_rel w hy star hFour other ψ K t

theorem adj_moved (K : Fin 4) (t : Fin degree) (h : adjPerm w hy star hFour other ψ K t ≠ t) :
    Adj w hy star hFour other ψ K t := by
  classical
  by_contra hNot
  apply h
  rw [adjPerm_apply]
  unfold adjFun
  rw [ite_eq_right hNot]

/-- **An adjusted sheet is pendant for its label**: the label is inactive on its block, and
the block carries a surviving occurrence. -/
theorem adj_pendant (K : Fin 4) (t : Fin degree) (h : Adj w hy star hFour other ψ K t) :
    IsDangling w.limit (w.limit.sourceEdge (star.edge K) t) ∧
      ∃ g : w.limit.SourceEdge, ¬ IsDangling w.limit g ∧
        Incident w.limit g (w.limit.sourceEndpoint (mergeVertex w) t) := by
  obtain ⟨hne, hns, hK⟩ := h
  have hInactive : K ∉ act w.limit star t := by
    have := not_mem_of_ne_ref _ _ _ hns K rfl hK
    rwa [eff_of_ne hne] at this
  refine ⟨isDangling_sourceEdge_of_not_mem_activeLabels w.limit star _ K hInactive t
    ((w.limit.vertexPartition (mergeVertex w)).rel_repr_left t), ?_⟩
  obtain ⟨L, hL⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  unfold act at hL
  obtain ⟨s', hs', hSurv⟩ := (mem_activeLabels_iff _ _ _ _).mp hL
  refine ⟨w.limit.sourceEdge (star.edge L) s', hSurv, ?_⟩
  have hEq : w.limit.sourceEndpoint (mergeVertex w) s' =
      w.limit.sourceEndpoint (mergeVertex w) t := by
    apply (w.limit.sourceEndpoint_eq_iff _ _ _).mpr
    exact ⟨rfl, hs'.symm⟩
  rw [← hEq]
  unfold Incident
  rw [sourceEnds_sourceEdge]
  rcases incident_star star L with h1 | h1
  · left
    simp only
    rw [h1]
  · right
    simp only
    rw [h1]

/-- The pendant limit automorphism re-pointing the `K` pendant. -/
noncomputable def beta (K : Fin 4) : GeometricStar.LimitIso hy w w :=
  pendantLimitIso w hy star K (adjPerm w hy star hFour other ψ K)
    (adjPerm_rel w hy star hFour other ψ K) (Adj w hy star hFour other ψ K)
    (adj_pendant w hy star hFour other ψ K) (adj_moved w hy star hFour other ψ K)

/-- All four re-pointings. -/
noncomputable def betaAll : GeometricStar.LimitIso hy w w :=
  (((beta w hy star hFour other ψ 0).trans (beta w hy star hFour other ψ 1)).trans
    (beta w hy star hFour other ψ 2)).trans (beta w hy star hFour other ψ 3)

/-- **The coherent limit isomorphism.** -/
noncomputable def coherentIso : GeometricStar.LimitIso hy other w :=
  ψ.trans (betaAll w hy star hFour other ψ)

theorem coherentIso_inheritedStar :
    W4WallExhaustion.inheritedStar other (coherentIso w hy star hFour other ψ) hFour star =
      W4WallExhaustion.inheritedStar other ψ hFour star := rfl

theorem coherentIso_index :
    W4WallExhaustion.index hFour star other (coherentIso w hy star hFour other ψ) =
      W4WallExhaustion.index hFour star other ψ := rfl

theorem beta_edgePerm_star (K L : Fin 4) :
    (beta w hy star hFour other ψ K).datum.edgePerm (star.edge L) =
      if K = L then adjPerm w hy star hFour other ψ K else Equiv.refl _ := by
  show GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved (mergeVertex w) (farEndpoint (mergeVertex w) (star.edge K))
      (farEndpoint_ne (incident_star star K)) (star.edge L)) (adjPerm w hy star hFour other ψ K) = _
  by_cases h : K = L
  · subst h
    rw [edgeMoved_self_eq_true (incident_star star K), ite_eq_left rfl]
    rfl
  · rw [edgeMoved_eq_false (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w)
      (incident_star star K) (incident_star star L)
      (fun he ↦ h (star.edge_injective he)), ite_eq_right h]
    rfl

theorem betaAll_edgePerm_star (L : Fin 4) (x : Fin degree) :
    (betaAll w hy star hFour other ψ).datum.edgePerm (star.edge L) x =
      adjPerm w hy star hFour other ψ L x := by
  change (beta w hy star hFour other ψ 3).datum.edgePerm (star.edge L)
    ((beta w hy star hFour other ψ 2).datum.edgePerm (star.edge L)
      ((beta w hy star hFour other ψ 1).datum.edgePerm (star.edge L)
        ((beta w hy star hFour other ψ 0).datum.edgePerm (star.edge L) x))) = _
  simp only [beta_edgePerm_star]
  fin_cases L <;> simp

/-- The transport isomorphism of `coherentIso` (its limit dictionary read against the
wall-anchored positions). -/
noncomputable abbrev phi : GeometricDatumIso other.limit w.limit :=
  (coherentIso w hy star hFour other ψ).datum.trans (GeometricDatumIso.refl w.limit).symm

theorem phi_edgePerm (e : (other.frame.limitTarget other.column).edges) (s : Fin degree) :
    (phi w hy star hFour other ψ).edgePerm e s =
      (betaAll w hy star hFour other ψ).datum.edgePerm (ψ.datum.targetEdge e)
        (ψ.datum.edgePerm e s) := rfl

/-- **`coherentIso` is coherent.** -/
theorem coherent_coherentIso :
    Coherent (W4WallExhaustion.inheritedStar other ψ hFour star) (phi w hy star hFour other ψ)
      (W4WallExhaustion.index hFour star other ψ) := by
  classical
  intro s L hns
  set Sm := W4WallExhaustion.inheritedStar other ψ hFour star
  set q := W4WallExhaustion.index hFour star other ψ
  set r := ref (eff (act other.limit Sm s)) q
  rw [phi_edgePerm, phi_edgePerm, hSψ, hSψ, betaAll_edgePerm_star, betaAll_edgePerm_star,
    adjPerm_apply, adjPerm_apply]
  have hActOf : ∀ K, act w.limit star (ψ.datum.edgePerm (Sm.edge K) s) =
      act other.limit Sm s := fun K ↦
    act_map Sm star ψ.datum (hAψ w hy hFour other ψ) (hSψ w hy star hFour other ψ)
      (InheritedLimitRows.limit_connected other) s _ (edgePerm_rel w hy star hFour other ψ K s)
  by_cases hLr : L = r
  · rw [hLr]
  by_cases hE : act other.limit Sm s = ∅
  · have hNotAdj : ∀ K, ¬ Adj w hy star hFour other ψ K (ψ.datum.edgePerm (Sm.edge K) s) := by
      intro K h
      exact h.1 ((hActOf K).trans hE)
    unfold adjFun
    rw [ite_eq_right (hNotAdj L), ite_eq_right (hNotAdj r)]
    exact eq_of_act_empty w.limit star (RegrowthWallInput.w4Input w hy star)
      ((hActOf L).trans hE)
      ((edgePerm_rel w hy star hFour other ψ L s).trans
        (edgePerm_rel w hy star hFour other ψ r s).symm)
  · have hAdjL : Adj w hy star hFour other ψ L (ψ.datum.edgePerm (Sm.edge L) s) := by
      refine ⟨(hActOf L).trans_ne hE, ?_, ?_⟩
      · rw [hActOf L]
        exact hns
      · rw [hActOf L]
        exact hLr
    have hNotAdjR : ¬ Adj w hy star hFour other ψ r (ψ.datum.edgePerm (Sm.edge r) s) := by
      intro h
      apply h.2.2
      rw [hActOf r]
    unfold adjFun
    rw [ite_eq_left hAdjL, ite_eq_right hNotAdjR, hActOf L, Equiv.symm_apply_apply]

end Coherence

/-! ## 12.  Exhaustion at every four-valent wall, and the `w4` family clause -/

section Exhaustion

open W4TargetPairings (FourStar)
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Every star member presents a decoupled transport at its own pairing**, along the
coherent re-pointing of any of its limit isomorphisms. -/
theorem nonempty_positionTransport (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))
    (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)
    (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w) :
    Nonempty (W4NonDiscreteStarCensus.PositionTransport w hy star hFour other
      (coherentIso w hy star hFour other ψ)
      (W4WallExhaustion.index hFour star other (coherentIso w hy star hFour other ψ))) :=
  nonempty_transportFree_of_coherent (W4WallExhaustion.inheritedStar other ψ hFour star) star
    (phi w hy star hFour other ψ)
    (W4WallExhaustion.map_merge other (coherentIso w hy star hFour other ψ) hFour)
    (W4WallExhaustion.inheritedStar_edge other (coherentIso w hy star hFour other ψ) hFour star)
    (InheritedLimitRows.limit_connected other)
    (memberInput w hy star hFour other (coherentIso w hy star hFour other ψ))
    (RegrowthWallInput.w4Input w hy star)
    (W4WallExhaustion.index hFour star other ψ)
    (W4NonDiscreteStarCensus.memberResolution w hy star hFour other
      (coherentIso w hy star hFour other ψ))
    (member_left_sameBlocks w hy star hFour other (coherentIso w hy star hFour other ψ))
    (member_right_sameBlocks w hy star hFour other (coherentIso w hy star hFour other ψ))
    (member_newEdge_sameBlocks w hy star hFour other (coherentIso w hy star hFour other ψ))
    (W4NonDiscreteStarCensus.memberPlacement w hy star hFour other
      (coherentIso w hy star hFour other ψ))
    (W4WallExhaustion.right_map hFour star other (coherentIso w hy star hFour other ψ))
    (coherent_coherentIso w hy star hFour other ψ)

/-- **Exhaustion at every four-valent wall**, discrete or not, with no hypothesis. -/
theorem exhausts (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))
    (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4) :
    W4NonDiscreteStarCensus.Exhausts w hy star :=
  W4NonDiscreteStarCensus.exhausts_of_transports w hy star hFour fun m ↦ by
    obtain ⟨ψ⟩ := m.specializes
    exact ⟨coherentIso w hy star hFour m.member ψ,
      nonempty_positionTransport w hy star hFour m.member ψ⟩

/-- **The W4 census at every four-valent wall**: the star is the set of nonsingular
pairings of Equation (1), each class carrying its term. -/
theorem census (w : Regrowth core y degree) (hy : Nondegenerate y)
    (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))
    (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4) :
    ∃ e : {q : Fin 3 // W4NonDiscreteStarCensus.Nonsingular w hy star q} ≃
        GeometricStar.Star hy w,
      ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
        (signedMult (W4StarParity.lab w hy star q.1).presentation).num.natAbs :=
  W4NonDiscreteStarCensus.census_of_exhausts w hy star (exhausts w hy star hFour)

/-- **The residue of `W4NonDiscreteStarCensus` is discharged**: non-discrete four-valent exhaustion, with no
hypothesis. -/
theorem w4NonDiscreteStarExhaustion (degree n p : ℕ) :
    W4NonDiscreteStarCensus.W4NonDiscreteStarExhaustion degree n p :=
  fun _ _ hy w hFour _ star ↦ exhausts w hy star hFour

/-- **The `w4` clause of `FamilyStarParity`, at every degree, core size and request, with
no hypothesis.** -/
theorem familyStarParity_w4_all (degree n p : ℕ) :
    RegrowthWallInput.FamilyStarParity degree n p .w4 :=
  W4StarParity.familyStarParity_w4_of_nonDiscrete
    (W4NonDiscreteStarCensus.nonDiscreteW4StarParity_of_exhaustion
      (w4NonDiscreteStarExhaustion degree n p))

/-- **The `w4` clause of `FamilyStarParity` at genus six and degree four, unconditional.** -/
theorem familyStarParity_w4 :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w4 :=
  W4NonDiscreteStarCensus.familyStarParity_w4_of_exhaustion
    (w4NonDiscreteStarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3))

end Exhaustion

end DraismaVargas.Count.W4NonDiscreteStarExhaustionProof
