import GenusSixExistence.BrillNoetherRank.Tripod.GluingOntoOpen
import GenusSixExistence.BrillNoetherRank.Tripod.GluingOntoShape

/-!
# Onto: every open glued member over the gadget is a gluing

The proof of `GluingClasses.exists_isGluingOf_of_memberIsGlued`, in two steps. Prose proof:
`Research/genus-six-brill-noether-rank.md`, §5.5 (The bijection, the onto step); section numbers
in this file refer to that note.

1. **The shape** (`exists_glueShape`, from `GluingOntoShape`): an open glued member
   `φ` over `Γ̃` at long legs is, up to a `GeometricDatumIso`, the glued datum `glueDatum D π` of a
   connected degree-four datum `D` at a non-dangling placement `π`, carrying the marks, the centre
   (in the new sheet) and the legs (`ShapeLabels`, the three clauses of `GluedLabels` that do not
   mention the member being glued). Its ingredients, all in `GluingOntoShape`: the dichotomy facts
   (`nonempty_gluedFacts`), the passages at the inner ends (`pass_of_arm`), the target
   (`GluingOntoTarget.exists_targetShape`), the construction of `D`, `π` and the isomorphism
   (`exists_shape`), the discrete arms (`arm_discrete`), the Y-sheet (`ySheet_singleton`, `Y′` is
   one sheet over `T̂`; `hairpin_turn`, the hairpins turn into it) and
   `connected_nonDangling_of_shape` (`D` connected, the marks on its core).
2. **The deletion** (`exists_isGluingOf_of_shape`): from the shape, a member `ψ` over
   `G̃` at the base request with `ψ.data = D`, open, of which `φ` is the gluing. Its pieces:
   * the structural fields of a full-dimensional presentation of `D`, read back from the glued
     datum stage by stage (this file): the target is connected (`graph_connected_of_T₆`), a tree
     (`T₆_genus`), saturated (`saturated_of_glueDatum`), Riemann--Hurwitz holds
     (`riemannHurwitz_of_glueDatum`) and `D` is trivalent (`trivalent_of_glueDatum`);
   * path ends, from a core identification (`hasPathEnds_of_ident`), and for the shape itself
     from the connected marked core (`GluingOntoIdent.hasPathEnds_of_shape`);
   * `det A_D ≠ 0`, from `|det A_N| · ∏ a_k = 8 |det A_D|` for a bare datum (`abs_det_glue_bare`,
     from `exists_refinementChain_bare`, the refinement chain S5a for a bare datum);
   * the core identification of `D` with the glued labels `old` and `row`
     (`exists_ident_of_shape`, from `GluingOntoIdent.exists_ident_of_shape_aux`);
   * openness at the base request (`openAt_of_shape`, from `GluingOntoOpen.mulVec_pieceCoords`:
     the coordinates of `D` are the sums of those of `φ` over the pieces).

The declarations live in the namespace `Gluing.Onto`.
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open Utilities.DeterminantExpansion

open TargetExpansion
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

namespace Onto

/-! ## 1. Reading the structure of `D` back from the glued datum -/

section Reverse

variable {T : CFGraph} {d : ℕ}

theorem num_edges_pos_of_mem {G : CFGraph} {e : G.V × G.V} (he : e ∈ G.edges) :
    0 < num_edges G e.1 e.2 :=
  Multiset.card_pos_iff_exists_mem.mpr ⟨e, Multiset.mem_filter.mpr ⟨he, Or.inl rfl⟩⟩

/-- **A target expansion is connected only if its target is**: contract the fresh vertex. -/
theorem graph_connected_of_expansion (wall : T.V) (right : T.edges → Bool)
    (h : graph_connected (TargetExpansion.graph T wall right)) : graph_connected T := by
  classical
  rintro S ⟨v, w, hv, hw⟩
  let S' : Finset (TargetExpansion.graph T wall right).V :=
    Finset.univ.filter fun x ↦ contractVertex T wall x ∈ S
  have hmem : ∀ x, x ∈ S' ↔ contractVertex T wall x ∈ S := fun x ↦ by simp [S']
  have key : ∀ x y : (TargetExpansion.graph T wall right).V,
      (x, y) ∈ expandedEdges T wall right →
      (contractVertex T wall x ∈ S ↔ contractVertex T wall y ∉ S) →
      0 < num_edges T (contractVertex T wall x) (contractVertex T wall y) := by
    intro x y hxy hS
    rcases Multiset.mem_cons.mp hxy with hnew | hold
    · simp only [newEnds] at hnew
      obtain ⟨rfl, rfl⟩ := hnew
      exact absurd hS (by simp [oldVertex, freshVertex, contractVertex])
    · obtain ⟨edge, -, hedge⟩ := Multiset.mem_map.mp hold
      simp only [oldEnds] at hedge
      obtain ⟨rfl, rfl⟩ := hedge
      rw [contract_expandedEndpoint, contract_expandedEndpoint]
      exact num_edges_pos_of_mem (e := (edge : T.V × T.V)) Multiset.coe_mem
  obtain ⟨a, ha, b, hb, hab⟩ := h S' ⟨oldVertex T v, oldVertex T w,
    (hmem _).mpr hv, fun h' ↦ hw ((hmem _).mp h')⟩
  have ha' := (hmem a).mp ha
  have hb' : contractVertex T wall b ∉ S := fun h' ↦ hb ((hmem b).mpr h')
  obtain ⟨pair, hpair⟩ := Multiset.card_pos_iff_exists_mem.mp hab
  obtain ⟨hpairMem, hpairEq⟩ := Multiset.mem_filter.mp hpair
  rcases hpairEq with rfl | rfl
  · exact ⟨_, ha', _, hb', key a b hpairMem ⟨fun _ ↦ hb', fun _ ↦ ha'⟩⟩
  · exact ⟨_, ha', _, hb', num_edges_pos_symm
      (key b a hpairMem ⟨fun h' ↦ absurd h' hb', fun h' ↦ absurd ha' h'⟩)⟩

theorem graph_connected_of_subdivTarget (t : T.edges) (h : graph_connected (subdivTarget T t)) :
    graph_connected T :=
  graph_connected_of_expansion _ _ h

theorem graph_connected_of_leafTarget (u : T.V) (h : graph_connected (leafTarget T u)) :
    graph_connected T :=
  graph_connected_of_expansion _ _ h

/-- The glued target is connected only if the target of `D` is. -/
theorem graph_connected_of_T₆ (π : Placement T d) (h : graph_connected π.T₆) :
    graph_connected T :=
  graph_connected_of_subdivTarget _ (graph_connected_of_subdivTarget _
    (graph_connected_of_subdivTarget _ (graph_connected_of_leafTarget _
      (graph_connected_of_leafTarget _ (graph_connected_of_leafTarget _ h)))))

/-- Riemann--Hurwitz at the old vertices of a refinement is that of `D`. -/
theorem riemannHurwitz_of_refineDatum (D : GluingDatum T d) (t : T.edges)
    (h : (refineDatum D t).RiemannHurwitz) : D.RiemannHurwitz := by
  intro w sheet
  have hw := h (subdivOld T t w) sheet
  rw [card_incidentEdges_eq_sum, sum_incidentEdges_subdivOld t w (fun _ ↦ (1 : ℤ))
      (fun _ ↦ (1 : ℤ)) (fun _ ↦ rfl) rfl,
    ← card_incidentEdges_eq_sum,
    sum_incidentEdges_subdivOld t w
      (fun e ↦ ((D.edgePartition e).blockCountWithin (D.vertexPartition w) sheet : ℤ)) _
      (fun e ↦ by rw [refineDatum_edgePartition_some]; rfl)
      (by rw [refineDatum_edgePartition_none]; rfl)] at hw
  exact hw

/-- Riemann--Hurwitz in the old sheets of `extendDatum D` is that of `D`. -/
theorem riemannHurwitz_of_extendDatum (D : GluingDatum T d)
    (h : (extendDatum D).RiemannHurwitz) : D.RiemannHurwitz := by
  intro v i
  have hv := h v i.castSucc
  change (∑ e ∈ GluingDatum.incidentEdges v,
        ((SheetOps.extendNew (D.edgePartition e)).blockCountWithin
          (SheetOps.extendNew (D.vertexPartition v)) i.castSucc : ℤ)) - 2 ≥
      ((SheetOps.extendNew (D.vertexPartition v)).blockCard i.castSucc : ℤ) *
        (((GluingDatum.incidentEdges v).card : ℤ) - 2) at hv
  simp only [SheetOps.blockCountWithin_extendNew_castSucc,
    SheetOps.blockCard_extendNew_castSucc] at hv
  exact hv

/-- Riemann--Hurwitz at the old vertices of `leafDatum D u a b` is that of `D`: at `u` the arm
adds `blockCard` to the left side and one edge to the right. -/
theorem riemannHurwitz_of_leafDatum (D : GluingDatum T d) (u : T.V) (a b : Fin d)
    (h : (leafDatum D u a b).RiemannHurwitz) : D.RiemannHurwitz := by
  intro w sheet
  have hw := h (leafOld T u w) sheet
  rw [card_incidentEdges_eq_sum, sum_incidentEdges_leafTarget, sum_incidentEdges_leafTarget] at hw
  simp only [leafDatum_edgePartition_none, leafDatum_edgePartition_some, blockCountWithin_discrete,
    leafDatum_vertexPartition_leafOld, (leafOld_injective T u).eq_iff, leafTip_ne_leafOld,
    or_false] at hw
  rw [card_incidentEdges_eq_sum, sum_incidentEdges_eq, sum_incidentEdges_eq]
  by_cases huw : u = w
  · simp only [huw, if_true] at hw
    nlinarith
  · simp only [huw, if_false] at hw
    linarith

/-- **Riemann--Hurwitz for `D`** from that of the glued datum, stage by stage. -/
theorem riemannHurwitz_of_glueDatum (D : GluingDatum T d) (π : Placement T d)
    (h : (glueDatum D π).RiemannHurwitz) : D.RiemannHurwitz :=
  riemannHurwitz_of_refineDatum _ _ (riemannHurwitz_of_refineDatum _ _
    (riemannHurwitz_of_refineDatum _ _ (riemannHurwitz_of_extendDatum _
      (riemannHurwitz_of_leafDatum _ _ _ _ (riemannHurwitz_of_leafDatum _ _ _ _
        (riemannHurwitz_of_leafDatum _ _ _ _ h))))))

/-- **The dimension count of `D` is saturated** when that of the glued datum is: six more target
edges, two more in the source genus, one more sheet. -/
theorem saturated_of_glueDatum (D : GluingDatum T d) (π : Placement T d) (hT0 : genus T = 0)
    (h : (π.T₆.edges.card : ℤ) =
      2 * genus (glueDatum D π).sourceGraph + 2 * ((d + 1 : ℕ) : ℤ) - 5) :
    (T.edges.card : ℤ) = 2 * genus D.sourceGraph + 2 * (d : ℤ) - 5 := by
  rw [genus_glueDatum D π hT0, π.T₆_edge_card] at h
  push_cast at h
  linarith

/-- The non-dangling valency of an old vertex of `D`, in `refine₃ D π`. -/
theorem nonDanglingValency_oldSV₃ (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected)
    (x : D.SourceVertex) :
    nonDanglingValency (refine₃ D π) (oldSV₃ D π x) = nonDanglingValency D x := by
  unfold oldSV₃
  rw [Refine.nonDanglingValency_oldSV _ _ (π.refine₂_connected D hD),
    Refine.nonDanglingValency_oldSV _ _ (π.refine₁_connected D hD),
    Refine.nonDanglingValency_oldSV _ _ hD]

/-- **`D` is trivalent** when the glued datum is. -/
theorem trivalent_of_glueDatum (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected)
    (hT : graph_connected T) (hπ : π.NonDangling D)
    (h : ∀ v, nonDanglingValency (glueDatum D π) v ≤ 3) (x : D.SourceVertex) :
    nonDanglingValency D x ≤ 3 := by
  have h1 := h (oldVertex₃ D π (oldSV₃ D π x))
  rw [nonDanglingValency_oldVertex₃ D π hD hT hπ, nonDanglingValency_oldSV₃ D π hD] at h1
  omega

end Reverse

/-! ## 2. Path ends from a core identification -/

section PathEnds

variable {n p : ℕ} {core : Core n p} {T : CFGraph.{0}} {d : ℕ}

/-- **A datum identified with a core has path ends**: every slot has a tail, a branch vertex the
stable path meets. -/
theorem hasPathEnds_of_ident (D : GluingDatum T d) (ident : CoreIdentification core D) :
    HasPathEnds D := by
  intro edge
  set j := ident.row edge.stablePath with hj
  set b := ident.vertex.symm (core.tail j) with hb
  have hinc := ident.incidence b j
  rw [hb, Equiv.apply_symm_apply] at hinc
  have hpos : 0 < incidenceCount D b.1 (ident.row.symm j) := by
    rw [← hb] at hinc
    rw [hinc]
    unfold coreIncidence
    simp
  obtain ⟨first, hfirst, hpath⟩ :=
    (StablePathCount.incidenceCount_pos_iff D b.1 _).mp hpos
  refine ⟨first, b.1, ?_, hfirst, ?_⟩
  · rw [hpath, hj, Equiv.symm_apply_apply]
  · have := b.2
    omega

end PathEnds

/-! ## 3. The determinant of a bare datum

`Gluing.abs_det_glueDatum_labelling` is stated for a member `ψ`, and uses of it only `ψ.data`,
its connectedness, its target, trivalence, path ends and labelling. Here is the same identity for
a bare datum, which the deletion needs before it has a member: `det A_D ≠ 0` is what makes `D` a
member. -/

section BareDet

variable {T : CFGraph} {d : ℕ} (D : GluingDatum T d) (π : Placement T d)

/-- The arm columns of a labelling of the glued datum, for a bare datum (`Gluing.ArmColumns`
without the member). -/
def ArmCols {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StableLengthMatrixLabelling (glueDatum D π) ι) (legRow : Fin 3 → ι) : Prop :=
  ∀ r k, GluingDatum.LengthMatrixPresentation.matrix L.presentation r
      (L.targetEdge.symm (π.armEdge k)) = if r = legRow k then 2 else 0

/-- The arm columns, in every labelling (`Gluing.exists_armColumns_glueDatum` for a bare datum). -/
theorem exists_armCols (hD : D.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
    (hπ : π.NonDangling D) (hEnds : HasPathEnds D) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StableLengthMatrixLabelling (glueDatum D π) ι) :
    ∃ legRow : Fin 3 → ι, Function.Injective legRow ∧ ArmCols D π L legRow := by
  have hconn := glueDatum_connected D π hD hT
  have hsurv := fun k ↦ hairpin_not_isDangling D π hD hT k
  refine ⟨fun k ↦ L.row (NonDanglingEdge.stablePath
      (⟨_, (hsurv k).1⟩ : NonDanglingEdge (glueDatum D π))), ?_, fun r k ↦ ?_⟩
  · intro k j hkj
    by_contra hne
    exact hairpinPath_ne_glue D π hD hT hT0 hπ hEnds hne (L.row.injective hkj)
  · exact matrix_armColumn D π L hconn k (hsurv k).1 (hsurv k).2 r

/-- **The non-leg rows are the rows of the old glued paths**, for a bare datum
(`Gluing.nonleg_cover` without the member; the same proof). -/
theorem nonleg_cover_bare {p : ℕ} (hD : D.Connected) (hT : graph_connected T)
    (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D)
    (hπ : π.NonDangling D) (LD : StableLengthMatrixLabelling D (Fin p))
    (L : StableLengthMatrixLabelling (glueDatum D π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) (hleg : Function.Injective legRow)
    (harm : ArmCols D π L legRow) :
    (∀ z, L.row (CutPaths.gluedPath D π hD hT hπ z) ∉ Set.range legRow) ∧
      ∀ i ∉ Set.range legRow, ∃ z, L.row (CutPaths.gluedPath D π hD hT hπ z) = i := by
  have hG := glueDatum_connected D π hD hT
  set g := CutPaths.gluedPath D π hD hT hπ with hgdef
  have hgcard := CutPaths.card_image_gluedPath hD hT hπ hT0 h3 hEnds
  rw [← hgdef] at hgcard
  have hp : Fintype.card (StablePath D) = p := by
    rw [Fintype.card_congr LD.row, Fintype.card_fin]
  have hlegRow : ∀ k, legRow k = L.row (NonDanglingEdge.stablePath
      (⟨_, (hairpin_not_isDangling D π hD hT k).1⟩ : NonDanglingEdge (glueDatum D π))) := by
    intro k
    have h := matrix_armColumn D π L hG k (hairpin_not_isDangling D π hD hT k).1
      (hairpin_not_isDangling D π hD hT k).2 (legRow k)
    rw [harm, if_pos rfl] at h
    by_contra hne
    rw [if_neg hne] at h
    norm_num at h
  have hnl : ∀ z, L.row (g z) ∉ Set.range legRow := by
    rintro z ⟨k, hk⟩
    rw [hlegRow k] at hk
    exact CutPaths.gluedPath_ne_hairpin hD hT hπ z k (L.row.injective hk).symm
  refine ⟨hnl, ?_⟩
  have hcardNL : Fintype.card {i // i ∉ Set.range legRow} = p + 3 := by
    have h := card_compl_range_add_three legRow hleg
    rw [Fintype.card_fin] at h
    omega
  classical
  intro i hi
  have hsub : Finset.univ.image (fun z ↦ L.row (g z)) ⊆
      Finset.univ.filter fun i ↦ i ∉ Set.range legRow := by
    intro j hj
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl z⟩
  have hc1 : (Finset.univ.image (fun z ↦ L.row (g z))).card = p + 3 := by
    have : Finset.univ.image (fun z ↦ L.row (g z)) = (Finset.univ.image g).image L.row := by
      rw [Finset.image_image]
      rfl
    rw [this, Finset.card_image_of_injective _ L.row.injective, hgcard, hp]
  have hc2 : (Finset.univ.filter fun i ↦ i ∉ Set.range legRow).card = p + 3 := by
    rw [← Fintype.card_subtype]
    convert hcardNL using 2
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc1, hc2])
  have hmem : i ∈ Finset.univ.filter fun i ↦ i ∉ Set.range legRow :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  rw [← heq] at hmem
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hmem
  exact ⟨z, hz⟩

/-- **(S5a) for a bare datum**: `Gluing.exists_refinementChain_glueDatum` with the member `ψ`
replaced by the fields of it that statement reads (`ψ.data`, connected, over a connected tree,
trivalent, with path ends, and its labelling). The same proof. -/
theorem exists_refinementChain_bare {p : ℕ} (hD : D.Connected) (hT : graph_connected T)
    (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D)
    (hπ : π.NonDangling D) (LD : StableLengthMatrixLabelling D (Fin p))
    (L : StableLengthMatrixLabelling (glueDatum D π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) (hleg : Function.Injective legRow)
    (harm : ArmCols D π L legRow)
    (e : {i // i ∉ Set.range legRow} ≃
      {j // j ∉ Set.range fun k ↦ L.targetEdge.symm (π.armEdge k)}) :
    ∃ (cls₁ : NonDanglingEdge (refineDatum D π.edge₀) → Option (Fin p))
      (cls₂ : NonDanglingEdge (refineDatum (refineDatum D π.edge₀) π.edge₁) →
        Option (Option (Fin p)))
      (cls₃ : NonDanglingEdge (refine₃ D π) → Option (Option (Option (Fin p)))),
      SplitsAt D π.edge₀ hD (fun x ↦ LD.row x.stablePath) cls₁ (π.markEdge₀ D hπ) ∧
        SplitsAt _ π.edge₁ (π.refine₁_connected D hD) cls₁ cls₂ (π.markEdge₁ D hD hπ) ∧
        SplitsAt _ π.edge₂ (π.refine₂_connected D hD) cls₂ cls₃ (π.markEdge₂ D hD hπ) ∧
        |((GluingDatum.LengthMatrixPresentation.matrix L.presentation).submatrix
            (fun i : {i // i ∉ Set.range legRow} ↦ i.1) (fun i ↦ (e i).1)).det| =
          |(clsMatrix (refine₃ D π) cls₃ (refineCol π.edge₂ (refineCol π.edge₁
            (refineCol π.edge₀ LD.targetEdge)))).det| := by
  obtain ⟨cls₁, cls₂, lab, s₁, s₂, s₃, hinj, -⟩ :=
    CutPaths.exists_cutLabels hD hT hπ hT0 h3 hEnds LD.row
  refine ⟨cls₁, cls₂, fun z ↦ lab (CutPaths.gluedPath D π hD hT hπ z), s₁, s₂, s₃, ?_⟩
  set g := CutPaths.gluedPath D π hD hT hπ with hgdef
  obtain ⟨-, hcover₀⟩ := nonleg_cover_bare D π hD hT hT0 h3 hEnds hπ LD L legRow hleg harm
  have hcover : ∀ i ∉ Set.range legRow, ∃ z, L.row (g z) = i := hcover₀
  have hcardNL : Fintype.card {i // i ∉ Set.range legRow} = p + 3 := by
    have h := card_compl_range_add_three legRow hleg
    rw [Fintype.card_fin] at h
    omega
  have hinj' : ∀ z z', lab (g z) = lab (g z') → g z = g z' := by
    classical
    intro z z' h
    exact hinj (by simp) (by simp) h
  -- the row bijection
  let β : {i // i ∉ Set.range legRow} → Option (Option (Option (Fin p))) := fun i ↦
    lab (L.row.symm i.1)
  have hβ : Function.Bijective β := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i i' h ↦ ?_, by rw [hcardNL]; simp⟩
    obtain ⟨z, hz⟩ := hcover i.1 i.2
    obtain ⟨z', hz'⟩ := hcover i'.1 i'.2
    have h' : lab (g z) = lab (g z') := by
      simp only [β, ← hz, ← hz', Equiv.symm_apply_apply] at h
      exact h
    apply Subtype.ext
    rw [← hz, ← hz', hinj' z z' h']
  have hβrow : ∀ z (i : {i // i ∉ Set.range legRow}), L.row (g z) = i.1 ↔ lab (g z) = β i := by
    intro z i
    constructor
    · intro h
      show lab (g z) = lab (L.row.symm i.1)
      rw [← h, Equiv.symm_apply_apply]
    · intro h
      obtain ⟨z', hz'⟩ := hcover i.1 i.2
      have h' : lab (g z) = lab (g z') := by
        rw [h]
        show lab (L.row.symm i.1) = lab (g z')
        rw [← hz', Equiv.symm_apply_apply]
      rw [hinj' z z' h', hz']
  -- the column bijection
  let δ : (π.T₃).edges → {j // j ∉ Set.range fun k ↦ L.targetEdge.symm (π.armEdge k)} :=
    fun ε ↦ ⟨L.targetEdge.symm (π.liftE₃ ε), by
      rintro ⟨k, hk⟩
      exact π.liftE₃_ne_armEdge ε k (L.targetEdge.symm.injective hk).symm⟩
  have hδ : Function.Bijective δ := by
    refine ⟨fun ε ε' h ↦ π.liftE₃_injective (L.targetEdge.symm.injective
      (congrArg Subtype.val h)), fun j ↦ ?_⟩
    rcases π.T₆_edge_cases (L.targetEdge j.1) with ⟨ε, hε⟩ | ⟨k, hk⟩
    · refine ⟨ε, Subtype.ext ?_⟩
      show L.targetEdge.symm (π.liftE₃ ε) = j.1
      rw [← hε, Equiv.symm_apply_apply]
    · refine absurd ⟨k, ?_⟩ j.2
      show L.targetEdge.symm (π.armEdge k) = j.1
      rw [← hk, Equiv.symm_apply_apply]
  set col₃ := refineCol π.edge₂ (refineCol π.edge₁ (refineCol π.edge₀ LD.targetEdge)) with hcol₃
  let γ := (Equiv.ofBijective δ hδ).symm.trans col₃.symm
  have hγ : ∀ j, L.targetEdge j.1 = π.liftE₃ (col₃ (γ j)) := by
    intro j
    show L.targetEdge j.1 = π.liftE₃ (col₃ (col₃.symm ((Equiv.ofBijective δ hδ).symm j)))
    rw [Equiv.apply_symm_apply]
    have hε := Equiv.apply_symm_apply (Equiv.ofBijective δ hδ) j
    set ε := (Equiv.ofBijective δ hδ).symm j
    have h1 : j.1 = L.targetEdge.symm (π.liftE₃ ε) := (congrArg Subtype.val hε).symm
    rw [h1, Equiv.apply_symm_apply]
  -- the residual block is the class matrix, reindexed
  have hblock : (GluingDatum.LengthMatrixPresentation.matrix L.presentation).submatrix
      (fun i : {i // i ∉ Set.range legRow} ↦ i.1) (fun i ↦ (e i).1) =
      (clsMatrix (refine₃ D π) (fun z ↦ lab (g z)) col₃).submatrix
        (Equiv.ofBijective β hβ) (e.trans γ) := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, matrix_eq_clsMatrix]
    simp only [clsMatrix]
    rw [CutPaths.sum_eq_sum_liftND hD hT hπ]
    · refine Finset.sum_congr rfl fun z _ ↦ ?_
      have hrow : L.row (CutPaths.liftND D π hD hT hπ z).stablePath = i.1 ↔
          lab (g z) = Equiv.ofBijective β hβ i := hβrow z i
      have hcol : (CutPaths.liftND D π hD hT hπ z).1.1.1 = L.targetEdge (e j).1 ↔
          z.1.1.1 = col₃ ((e.trans γ) j) := by
        rw [hγ]
        exact π.liftE₃_injective.eq_iff
      by_cases hc : lab (g z) = Equiv.ofBijective β hβ i ∧ z.1.1.1 = col₃ ((e.trans γ) j)
      · rw [if_pos ((and_congr hrow hcol).mpr hc), if_pos hc]
        show (1 : ℚ) / ((glueDatum D π).sourceEdgeIndex (liftSE D π z.1) : ℚ) = _
        rw [CutPaths.sourceEdgeIndex_liftSE z.1]
      · rw [if_neg (fun h ↦ hc ((and_congr hrow hcol).mp h)), if_neg hc]
    · intro x hx
      rw [if_neg]
      rintro ⟨hrow, -⟩
      obtain ⟨z, hz⟩ := hcover i.1 i.2
      rw [← hz] at hrow
      exact hx ((CutPaths.isOld_iff_of_stablePath_eq hD hT hπ (L.row.injective hrow)).mpr
        (CutPaths.isOld_liftND hD hT hπ z))
  rw [hblock, abs_det_submatrix_equiv]

/-- **(S5) for a bare datum**: the residual block, `|det A'| · ∏ a_k = |det A_D|`. The proof of
`Gluing.abs_det_residual_glueDatum`, verbatim. -/
theorem abs_det_residual_bare {p : ℕ} (hD : D.Connected) (hT : graph_connected T)
    (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D)
    (hπ : π.NonDangling D) (LD : StableLengthMatrixLabelling D (Fin p))
    (L : StableLengthMatrixLabelling (glueDatum D π) (Fin (p + 1 + 1 + 1 + 3)))
    (legRow : Fin 3 → Fin (p + 1 + 1 + 1 + 3)) (hleg : Function.Injective legRow)
    (harm : ArmCols D π L legRow)
    (e : {i // i ∉ Set.range legRow} ≃
      {j // j ∉ Set.range fun k ↦ L.targetEdge.symm (π.armEdge k)}) :
    |((GluingDatum.LengthMatrixPresentation.matrix L.presentation).submatrix
        (fun i : {i // i ∉ Set.range legRow} ↦ i.1) (fun i ↦ (e i).1)).det| *
      ∏ k, (π.markIndex D k : ℚ) =
        |(GluingDatum.LengthMatrixPresentation.matrix LD.presentation).det| := by
  obtain ⟨cls₁, cls₂, cls₃, h₁, h₂, h₃, hres⟩ :=
    exists_refinementChain_bare D π hD hT hT0 h3 hEnds hπ LD L legRow hleg harm e
  have s₁ := abs_det_clsMatrix_refine _ _ hD _ LD.targetEdge _ _ h₁
  have s₂ := abs_det_clsMatrix_refine _ _ (π.refine₁_connected _ hD) _
    (refineCol π.edge₀ LD.targetEdge) _ _ h₂
  have s₃ := abs_det_clsMatrix_refine _ _ (π.refine₂_connected _ hD) _
    (refineCol π.edge₁ (refineCol π.edge₀ LD.targetEdge)) _ _ h₃
  rw [π.sourceEdgeIndex_markEdge₀] at s₁
  rw [π.sourceEdgeIndex_markEdge₁ _ hD] at s₂
  rw [π.sourceEdgeIndex_markEdge₂ _ hD] at s₃
  rw [hres, Fin.prod_univ_three, matrix_eq_clsMatrix, ← s₁, ← s₂, ← s₃]
  ring

/-- **`|det A_N| · ∏ a_k = 8 |det A_D|`, for a bare datum** (`Gluing.abs_det_glueDatum_labelling`
without the member): expand along the arm columns, then the residual block. -/
theorem abs_det_glue_bare {p : ℕ} (hD : D.Connected) (hT : graph_connected T)
    (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D)
    (hπ : π.NonDangling D) (LD : StableLengthMatrixLabelling D (Fin p))
    (L : StableLengthMatrixLabelling (glueDatum D π) (Fin (p + 1 + 1 + 1 + 3))) :
    |(GluingDatum.LengthMatrixPresentation.matrix L.presentation).det| *
        ∏ k, (π.markIndex D k : ℚ) =
      8 * |(GluingDatum.LengthMatrixPresentation.matrix LD.presentation).det| := by
  classical
  obtain ⟨legRow, hleg, harm⟩ := exists_armCols D π hD hT hT0 hπ hEnds L
  have harmInj : Function.Injective fun k ↦ L.targetEdge.symm (π.armEdge k) :=
    L.targetEdge.symm.injective.comp π.armEdge_injective
  have hcard : Fintype.card {i // i ∉ Set.range legRow} =
      Fintype.card {j // j ∉ Set.range fun k ↦ L.targetEdge.symm (π.armEdge k)} := by
    have h1 := card_compl_range_add_three legRow hleg
    have h2 := card_compl_range_add_three _ harmInj
    omega
  let e := Fintype.equivOfCardEq hcard
  rw [abs_det_eq_of_doubled_columns _ legRow _ hleg harmInj harm e, mul_assoc,
    abs_det_residual_bare D π hD hT hT0 h3 hEnds hπ LD L legRow hleg harm e]

/-- The index of the old source edge under a mark is positive. -/
theorem markIndex_pos (k : Fin 3) : 0 < π.markIndex D k :=
  SheetPartition.blockCard_pos _ _

/-- **`det A_D ≠ 0`** as soon as some labelling of the glued datum is nonsingular. -/
theorem det_ne_zero_bare {p : ℕ} (hD : D.Connected) (hT : graph_connected T)
    (hT0 : genus T = 0) (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D)
    (hπ : π.NonDangling D) (LD : StableLengthMatrixLabelling D (Fin p))
    (L : StableLengthMatrixLabelling (glueDatum D π) (Fin (p + 1 + 1 + 1 + 3)))
    (hL : (GluingDatum.LengthMatrixPresentation.matrix L.presentation).det ≠ 0) :
    (GluingDatum.LengthMatrixPresentation.matrix LD.presentation).det ≠ 0 := by
  intro h0
  have h := abs_det_glue_bare D π hD hT hT0 h3 hEnds hπ LD L
  rw [h0, abs_zero, mul_zero] at h
  have hprod : (∏ k, (π.markIndex D k : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ by exact_mod_cast (markIndex_pos D π k).ne'
  exact hL (abs_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hprod))

end BareDet

/-! ## 4. The shape, and the deletion -/

section Deletion

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p}

/-- **The shape of an open glued member** (§5.5, the onto step): at
long legs, an open glued member over `Γ̃` is the glued datum of a connected degree-four datum at a
placement of the marks on its core, with the marks, the centre and the legs where the gluing
puts them. -/
theorem exists_glueShape (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (φ : FibreMember (tripodCore core s) y (3 + 2)) (hφ : φ.Open) (hGlued : MemberIsGlued φ) :
    ∃ (T : CFGraph.{0}) (D : GluingDatum T (2 + 2)) (π : Placement T (2 + 2)),
      D.Connected ∧ π.NonDangling D ∧
        ∃ Ξ : GeometricDatumIso (glueDatum D π) φ.data, ShapeLabels s D π φ.ident Ξ := by
  -- `GluingOntoShape`: the dichotomy facts (`nonempty_gluedFacts`), the sheet shape
  -- (`sheetShape`: the Y-sheet `ySheet_shape`, and the passages
  -- `pass_of_arm`), the
  -- construction of `T`, `D`, `π` and `Ξ` (`exists_shape`), and the
  -- connectedness of `D` with the marks on its core (`connected_nonDangling_of_shape`).
  obtain ⟨G⟩ := nonempty_gluedFacts φ hGlued
  have hS := sheetShape hcubic hconn hgenus hpos hlong φ hφ hGlued G
  obtain ⟨T, D, π, Ξ, hL⟩ := exists_shape φ G hS
  obtain ⟨hD, hπ⟩ := connected_nonDangling_of_shape hconn φ Ξ hL
  exact ⟨T, D, π, hD, hπ, Ξ, hL⟩

/-- **The core identification of the deletion** (§5.5): the stable graph of `D`
is `G̃`, with the glued labels. Branch vertices of `D` are the old branch vertices of the glued
datum, labelled `oldLabel v` by `φ.ident`; a stable path of `D` is labelled by the merged slot
of the glued paths through its pieces (`GluingInjective.pieceLabel_eq_of_consecutive`). -/
theorem exists_ident_of_shape (hcubic : core.Cubic) (hconn : core.Connected)
    {T : CFGraph.{0}} {D : GluingDatum T (2 + 2)}
    {π : Placement T (2 + 2)} (hD : D.Connected) (hπ : π.NonDangling D)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (φ : FibreMember (tripodCore core s) y (3 + 2))
    (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ) :
    ∃ ident : CoreIdentification core D,
      (∀ b : BranchVertex D, (φ.ident.vertex.symm (oldLabel (ident.vertex b))).1 =
        Ξ.sourceVertexEquiv (π.oldSourceVertex D b.1)) ∧
      ∀ e : NonDanglingEdge D, ∃ e' : NonDanglingEdge φ.data,
        e'.1 = Ξ.sourceEdgeEquiv (π.oldSourceEdge D e.1) ∧
          mergeSlot s (φ.ident.row e'.stablePath) = some (ident.row e.stablePath) := by
  -- `GluingOntoIdent`: the structural facts about the glued datum come from `φ` through `Ξ`
  -- (`GeometricMultiplicity.transportFullDim`); trivalence of `D` from the glued datum
  -- (`trivalent_of_glueDatum`); path ends of `D` from the connected marked core
  -- (`hasPathEnds_of_shape`); and the identification itself from `exists_ident_of_shape_aux`.
  set fdN := GeometricMultiplicity.transportFullDim Ξ.symm φ.fullDim with hfdN
  have hT : graph_connected T := graph_connected_of_T₆ π fdN.targetConnected
  have hT0 : genus T = 0 := π.T₆_genus.symm.trans fdN.targetGenus
  have h3 := trivalent_of_glueDatum D π hD hT hπ fdN.trivalent
  have hEnds := hasPathEnds_of_shape hD hT hπ Ξ hS hconn fdN.pathEnds
  exact exists_ident_of_shape_aux hD hT hπ hT0 Ξ hS hcubic h3 hEnds

/-- **`D` is full-dimensional**, given a core identification: the structural fields from the
glued datum (section 1), path ends from the identification, and `det A_D ≠ 0` from
`|det A_N| · ∏ a_k = 8 |det A_D|`. -/
theorem nonempty_fullDim_of_shape {T : CFGraph.{0}} {D : GluingDatum T (2 + 2)}
    {π : Placement T (2 + 2)} (hD : D.Connected) (hπ : π.NonDangling D)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (φ : FibreMember (tripodCore core s) y (3 + 2))
    (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (ident : CoreIdentification core D) :
    Nonempty (FullDimensionalSourcePresentation D (Fin p)) := by
  classical
  set fdN := GeometricMultiplicity.transportFullDim Ξ.symm φ.fullDim with hfdN
  have hT : graph_connected T := graph_connected_of_T₆ π fdN.targetConnected
  have hT0 : genus T = 0 := π.T₆_genus.symm.trans fdN.targetGenus
  have h3 := trivalent_of_glueDatum D π hD hT hπ fdN.trivalent
  have hEnds := hasPathEnds_of_ident D ident
  have h6 : Fintype.card π.T₆.edges = p + 1 + 1 + 1 + 3 := by
    rw [Fintype.card_congr fdN.labelling.targetEdge.symm, Fintype.card_fin]
  have hcardT : Fintype.card T.edges = p := by
    rw [Multiset.card_coe] at h6 ⊢
    rw [π.T₆_edge_card] at h6
    omega
  let LD : StableLengthMatrixLabelling D (Fin p) :=
    ⟨(Fintype.equivFinOfCardEq hcardT).symm, ident.row⟩
  exact ⟨{ valid := ⟨hD, riemannHurwitz_of_glueDatum D π fdN.valid.2⟩
           targetConnected := hT
           targetGenus := hT0
           saturated := saturated_of_glueDatum D π hT0 fdN.saturated
           labelling := LD
           det_ne_zero := det_ne_zero_bare D π hD hT hT0 h3 hEnds hπ LD fdN.labelling
             fdN.det_ne_zero
           trivalent := h3
           pathEnds := hEnds }⟩

/-- **The deletion is open at the base request** (§5.5, the onto step: its coordinates are
sums of coordinates of `φ`, so they are positive): the coordinate of `D` on a target edge `t` is the
sum of the coordinates of `φ` on the pieces of `t`. -/
theorem openAt_of_shape {T : CFGraph.{0}} {D : GluingDatum T (2 + 2)}
    {π : Placement T (2 + 2)} (hD : D.Connected) (hπ : π.NonDangling D)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (φ : FibreMember (tripodCore core s) y (3 + 2))
    (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ)
    (fd : FullDimensionalSourcePresentation D (Fin p)) (ident : CoreIdentification core D)
    (hrow : ∀ e : NonDanglingEdge D, ∃ e' : NonDanglingEdge φ.data,
      e'.1 = Ξ.sourceEdgeEquiv (π.oldSourceEdge D e.1) ∧
        mergeSlot s (φ.ident.row e'.stablePath) = some (ident.row e.stablePath))
    (hφ : φ.Open) :
    Frame.OpenAt (⟨T, D, fd, ident⟩ : Frame core (2 + 2)) (baseRequest s y) := by
  -- `GluingOntoOpen`: the piece sums of the coordinates of `φ` solve the realisation equation
  -- of `D` at the base request (`mulVec_pieceCoords`), so they are its coordinates
  -- (`FibreMember.coords_unique`), and they are positive (`pieceCoords_pos`).
  set fdN := GeometricMultiplicity.transportFullDim Ξ.symm φ.fullDim with hfdN
  have hT : graph_connected T := graph_connected_of_T₆ π fdN.targetConnected
  have hT0 : genus T = 0 := π.T₆_genus.symm.trans fdN.targetGenus
  let κ : Frame core (2 + 2) := ⟨T, D, fd, ident⟩
  have hsolve : (κ.member (baseRequest s y)).matrix.mulVec (pieceCoords Ξ fd.labelling) =
      fun r ↦ baseRequest s y ((κ.member (baseRequest s y)).ident.row
        ((κ.member (baseRequest s y)).fullDim.labelling.row.symm r)) := by
    funext r
    exact mulVec_pieceCoords hD hT hπ hT0 Ξ hS fd ident hrow r
  have huniq := (κ.member (baseRequest s y)).coords_unique _ hsolve
  intro c
  show 0 < (κ.member (baseRequest s y)).coords c
  rw [← huniq]
  exact pieceCoords_pos Ξ hφ fd.labelling c

/-- **The deletion** (§5.5, the onto step): a glued datum with the shape of
a gluing is the gluing of an open member over `G̃` at the base request. -/
theorem exists_isGluingOf_of_shape (hcubic : core.Cubic) (hconn : core.Connected)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    {φ : FibreMember (tripodCore core s) y (3 + 2)} (hφ : φ.Open) {T : CFGraph.{0}}
    (D : GluingDatum T (2 + 2)) (π : Placement T (2 + 2)) (hD : D.Connected)
    (hπ : π.NonDangling D) (Ξ : GeometricDatumIso (glueDatum D π) φ.data)
    (hS : ShapeLabels s D π φ.ident Ξ) :
    ∃ ψ : FibreMember core (baseRequest s y) (2 + 2), ψ.Open ∧ IsGluingOf s ψ φ := by
  obtain ⟨ident, hold, hrow⟩ := exists_ident_of_shape hcubic hconn hD hπ φ Ξ hS
  obtain ⟨fd⟩ := nonempty_fullDim_of_shape hD hπ φ Ξ ident
  let κ : Frame core (2 + 2) := ⟨T, D, fd, ident⟩
  exact ⟨κ.member (baseRequest s y), openAt_of_shape hD hπ φ Ξ hS fd ident hrow hφ, π, hπ, Ξ,
    ⟨hold, hS.mark, hS.centre, hrow, hS.leg⟩⟩

end Deletion

end Onto

end GenusSixExistence.Tripod.Gluing

end
