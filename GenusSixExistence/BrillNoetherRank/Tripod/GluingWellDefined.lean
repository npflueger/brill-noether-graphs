import GenusSixExistence.BrillNoetherRank.Tripod.GluingOntoOpen
import GenusSixExistence.BrillNoetherRank.Tripod.GluingLayoutStages

/-!
# Well-definedness of the gluing: the placement is forced

The proof of `GluingClasses.nonempty_iso_of_isGluingOf_self` from one geometric statement and one
corner case. Prose proof: `Research/genus-six-brill-noether-rank.md`, §5.5 (The bijection,
"Well defined"); section numbers in this file refer to that note. Two open gluings `φ`, `φ'` of
one member `ψ` over `G̃`, at placements `π`, `π'`, are compared in three steps.

* **The placement is forced** (`placement_forced`, in `GluingLayoutStages`): when no mark
  sits on a loop slot of `G̃` (`MarksOffLoops`), `π'` is `π` with each mark moved to another sheet
  of the same source edge.
* **A change of sheet within a block** (`exists_sheetIso`): such placements give
  isomorphic glued data, by the transposition of the two sheets on the arm and at the tip only, and
  the glued labels move along it (`gluedLabels_sheetIso`).
* **One placement** (`nonempty_iso_of_samePlacement`): two labelled identifications with
  the glued labels at one placement agree. Every vertex label is pinned: old branch vertices and
  marks by the clauses `old` and `mark`, the centre as the only branch vertex of the new sheet
  (`Onto.newVertex_eq_centre`). A leg is pinned by the clause `leg`. A G-slot is pinned by its
  merged label (`pieceLabel_eq`) and its incidences, read through the pinned vertex labels: two
  pieces of one slot of `G̃` with the same ends in the marked core are equal
  (`PiecesDetermined`), which holds when no mark sits on a loop slot
  (`piecesDetermined_of_marksOffLoops`).

A mark on a loop slot of `G̃` does not arise. On a loop a mark would cut it into two pieces with
the same ends, and the vertex labels would not pin down the identification of the glued datum
with `Γ̃`. But `G̃` is loopless (`nonempty_iso_of_isGluingOf_self`, hypothesis `hloop`, which
`exists_gluing` takes from `TripodModel.loopless`), and then no mark sits on a loop slot
(`marksOffLoops_of_loopless`).
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

open TargetExpansion
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

namespace WellDefined

/-! ## 1. Pieces of one slot with the same ends -/

section Slots

variable {m q : ℕ}

/-- Two slots of a core with the same unordered ends. -/
def SameEnds (C : Core m q) (j j' : Fin q) : Prop :=
  (C.tail j = C.tail j' ∧ C.head j = C.head j') ∨ (C.tail j = C.head j' ∧ C.head j = C.tail j')

/-- Equal incidence profiles mean equal unordered ends. -/
theorem sameEnds_of_coreIncidence (C : Core m q) {j j' : Fin q}
    (h : ∀ u, coreIncidence C u j = coreIncidence C u j') : SameEnds C j j' := by
  have h1 := h (C.tail j)
  have h2 := h (C.head j)
  unfold coreIncidence at h1 h2
  by_cases a : C.tail j' = C.tail j
  · left
    refine ⟨a.symm, ?_⟩
    rw [a] at h2
    by_cases e : C.head j' = C.head j
    · exact e.symm
    · rw [if_neg e] at h2
      split_ifs at h2 <;> omega
  · right
    rw [if_pos rfl, if_neg a] at h1
    by_cases b : C.head j' = C.tail j
    · refine ⟨b.symm, ?_⟩
      have hne : C.head j ≠ C.tail j := by
        intro hh
        rw [if_pos hh, if_pos b] at h1
        omega
      rw [if_neg (Ne.symm hne), if_pos rfl, b, if_neg (Ne.symm hne)] at h2
      by_cases c : C.tail j' = C.head j
      · exact c.symm
      · rw [if_neg c] at h2
        omega
    · rw [if_neg b] at h1
      split_ifs at h1 <;> omega

/-- **One subdivision of a slot that is not a loop**: two slots of `subdivide C e` with the same
ends are equal, or old slots of `C` with the same ends. -/
theorem sameEnds_subdivide {C : Core m q} (e : Fin q) (hC : C.tail e ≠ C.head e)
    {j j' : Fin (q + 1)} (h : SameEnds (subdivide C e) j j') :
    j = j' ∨ ∃ a a' : Fin q, j = a.castSucc ∧ j' = a'.castSucc ∧ SameEnds C a a' := by
  have hcs : ∀ v : Fin m, v.castSucc ≠ Fin.last m := fun v ↦ (Fin.castSucc_lt_last v).ne
  induction j using Fin.lastCases with
  | last =>
    induction j' using Fin.lastCases with
    | last => exact Or.inl rfl
    | cast a' =>
      exfalso
      simp only [SameEnds, subdivide_tail_last, subdivide_head_last, subdivide_tail_castSucc,
        subdivide_head_castSucc] at h
      rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact hcs _ h1.symm
      · split_ifs at h1 with ha
        · subst ha
          exact hC (Fin.castSucc_injective _ h2).symm
        · exact hcs _ h1.symm
  | cast a =>
    induction j' using Fin.lastCases with
    | last =>
      exfalso
      simp only [SameEnds, subdivide_tail_last, subdivide_head_last, subdivide_tail_castSucc,
        subdivide_head_castSucc] at h
      rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact hcs _ h1
      · split_ifs at h2 with ha
        · subst ha
          exact hC (Fin.castSucc_injective _ h1)
        · exact hcs _ h2
    | cast a' =>
      simp only [SameEnds, subdivide_tail_castSucc, subdivide_head_castSucc,
        Fin.castSucc_inj] at h
      by_cases ha : a = e
      · by_cases ha' : a' = e
        · exact Or.inl (by rw [ha, ha'])
        · exfalso
          rw [if_pos ha, if_neg ha'] at h
          rcases h with ⟨-, h⟩ | ⟨-, h⟩
          · exact hcs _ h.symm
          · exact hcs _ h.symm
      · by_cases ha' : a' = e
        · exfalso
          rw [if_neg ha, if_pos ha'] at h
          rcases h with ⟨-, h⟩ | ⟨h, -⟩
          · exact hcs _ h
          · exact hcs _ h
        · rw [if_neg ha, if_neg ha'] at h
          simp only [Fin.castSucc_inj] at h
          exact Or.inr ⟨a, a', rfl, rfl, h⟩

end Slots

section Pieces

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p}

/-- **The pieces of one slot of `G̃` are told apart by their ends** in the marked core. This fails
only for a mark alone on a loop slot, whose two pieces both run from the loop's vertex to the
mark. -/
def PiecesDetermined (core : Core n p) (s : MarkSlots p) : Prop :=
  ∀ i i' : Fin (p + 1 + 1 + 1),
    mergeOne s.first (mergeOne s.second (mergeOne s.third i)) =
      mergeOne s.first (mergeOne s.second (mergeOne s.third i')) →
    SameEnds (markedCore core s) i i' → i = i'

/-- **Each mark sits on a slot that is not a loop**, at the stage it is placed: no slot of `G̃`
carrying a mark is a loop. -/
def MarksOffLoops (core : Core n p) (s : MarkSlots p) : Prop :=
  core.tail s.first ≠ core.head s.first ∧
    (subdivide core s.first).tail s.second ≠ (subdivide core s.first).head s.second ∧
    (subdivide (subdivide core s.first) s.second).tail s.third ≠
      (subdivide (subdivide core s.first) s.second).head s.third

theorem marksOffLoops_of_loopless (h : ∀ i, core.tail i ≠ core.head i) : MarksOffLoops core s :=
  ⟨h _, subdivide_loopless core s.first h _,
    subdivide_loopless _ s.second (subdivide_loopless core s.first h) _⟩

/-- **When no mark sits on a loop slot, the pieces are determined.** -/
theorem piecesDetermined_of_marksOffLoops (h : MarksOffLoops core s) :
    PiecesDetermined core s := by
  intro i i' hm he
  rcases sameEnds_subdivide s.third h.2.2 he with hii | ⟨a, a', rfl, rfl, he₂⟩
  · exact hii
  rw [mergeOne_castSucc, mergeOne_castSucc] at hm
  rcases sameEnds_subdivide s.second h.2.1 he₂ with haa | ⟨b, b', rfl, rfl, he₁⟩
  · rw [haa]
  rw [mergeOne_castSucc, mergeOne_castSucc] at hm
  rcases sameEnds_subdivide s.first h.1 he₁ with hbb | ⟨c, c', rfl, rfl, -⟩
  · rw [hbb]
  rw [mergeOne_castSucc, mergeOne_castSucc] at hm
  rw [hm]

/-- **Without a loop in `G̃` the pieces are determined.** -/
theorem piecesDetermined_of_loopless (h : ∀ i, core.tail i ≠ core.head i) :
    PiecesDetermined core s :=
  piecesDetermined_of_marksOffLoops (marksOffLoops_of_loopless h)

theorem mergeSlot_legSlot (k : Fin 3) : mergeSlot s (legSlot p k) = none := by
  unfold mergeSlot
  rw [dif_neg (by simp only [legSlot, Fin.val_natAdd]; omega)]

/-- Two G-slots of `Γ̃` with the same ends have the same ends in the marked core. -/
theorem sameEnds_markedCore {i i' : Fin (p + 1 + 1 + 1)}
    (h : SameEnds (tripodCore core s) (Fin.castAdd 3 i) (Fin.castAdd 3 i')) :
    SameEnds (markedCore core s) i i' := by
  simp only [SameEnds, Dichotomy.tripodCore_tail_castAdd, Dichotomy.tripodCore_head_castAdd,
    Fin.castSucc_inj] at h
  exact h

end Pieces

/-! ## 2. Two labelled identifications at one placement -/

section SamePlacement

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {d : ℕ} {yG : Fin p → ℚ}
  {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}

theorem shapeLabels_of_gluedLabels {ψ : FibreMember core yG d} {π : Placement ψ.target d}
    {target' : CFGraph.{0}} {data' : GluingDatum target' (d + 1)}
    {ident' : CoreIdentification (tripodCore core s) data'}
    {iso : GeometricDatumIso (glueDatum ψ.data π) data'} (h : GluedLabels s ψ π ident' iso) :
    Onto.ShapeLabels s ψ.data π ident' iso :=
  ⟨h.mark, h.centre, h.leg⟩

/-- **Every vertex label is pinned by the glued labels**: through two gluing isomorphisms at one
placement, the branch vertices with one label correspond. -/
theorem vertex_agree {ψ : FibreMember core yG d} {π : Placement ψ.target d}
    {φ φ' : FibreMember (tripodCore core s) y (d + 1)}
    (iso : GeometricDatumIso (glueDatum ψ.data π) φ.data)
    (iso' : GeometricDatumIso (glueDatum ψ.data π) φ'.data)
    (hL : GluedLabels s ψ π φ.ident iso) (hL' : GluedLabels s ψ π φ'.ident iso')
    (L : Fin (n + 1 + 1 + 1 + 1)) :
    iso'.sourceVertexEquiv (iso.sourceVertexEquiv.symm (φ.ident.vertex.symm L).1) =
      (φ'.ident.vertex.symm L).1 := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  by_cases hL1 : L.val < n
  · have hLv : L = oldLabel (ψ.ident.vertex (ψ.ident.vertex.symm ⟨L.val, hL1⟩)) := by
      rw [Equiv.apply_symm_apply]; exact Fin.ext rfl
    rw [hLv, hL.old, hL'.old, Equiv.symm_apply_apply]
  · by_cases hL2 : L.val < n + 3
    · have hLk : L = tripodMark n ⟨L.val - n, by omega⟩ :=
        Fin.ext (by simp only [tripodMark, markVertex, Fin.val_castSucc]; omega)
      rw [hLk, hL.mark, hL'.mark, Equiv.symm_apply_apply]
    · have hLc : L = centre n := Fin.ext (by simp only [centre, Fin.val_last]; omega)
      subst hLc
      have hT0 := ψ.fullDim.targetGenus
      obtain ⟨u, hu⟩ := Onto.exists_centre_eq_newVertex hD hT iso' (shapeLabels_of_gluedLabels hL')
      have h3 := Onto.three_le_symm hD hT iso' (φ'.ident.vertex.symm (centre n))
      rw [hu] at h3
      have hc := Onto.newVertex_eq_centre hD hT hT0 iso (shapeLabels_of_gluedLabels hL) h3
      rw [← hc, ← hu, Equiv.apply_symm_apply]

/-- **Two gluings at one placement are isomorphic over `Γ̃`** when the pieces of each slot of `G̃`
are told apart by their ends. The isomorphism is the composite of the two gluing isomorphisms. -/
theorem nonempty_iso_of_samePlacement {ψ : FibreMember core yG d} {π : Placement ψ.target d}
    (hπ : π.NonDangling ψ.data) {φ φ' : FibreMember (tripodCore core s) y (d + 1)}
    (iso : GeometricDatumIso (glueDatum ψ.data π) φ.data)
    (iso' : GeometricDatumIso (glueDatum ψ.data π) φ'.data)
    (hL : GluedLabels s ψ π φ.ident iso) (hL' : GluedLabels s ψ π φ'.ident iso')
    (hdet : PiecesDetermined core s) : Nonempty (GeometricMemberIso φ φ') := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hT0 := ψ.fullDim.targetGenus
  have hG := glueDatum_connected ψ.data π hD hT
  have hφc := φ.fullDim.valid.1
  set Ξ := iso.symm.trans iso' with hΞ
  have hV : ∀ L, Ξ.sourceVertexEquiv (φ.ident.vertex.symm L).1 = (φ'.ident.vertex.symm L).1 :=
    fun L ↦ vertex_agree iso iso' hL hL' L
  have hΞP : ∀ Q, Ξ.stablePathEquiv hφc (iso.stablePathEquiv hG Q) =
      iso'.stablePathEquiv hG Q := by
    intro Q
    rw [hΞ, GeometricDatumIso.stablePathEquiv_trans _ _ hφc hG,
      GeometricDatumIso.stablePathEquiv_symm iso hG hφc, Equiv.trans_apply,
      Equiv.symm_apply_apply]
  refine ⟨⟨Ξ, fun b ↦ ?_, fun Q ↦ ?_⟩⟩
  · -- vertices
    have hb : Ξ.branchVertexEquiv hφc b = φ'.ident.vertex.symm (φ.ident.vertex b) := by
      apply Subtype.ext
      show Ξ.sourceVertexEquiv b.1 = _
      have := hV (φ.ident.vertex b)
      rw [Equiv.symm_apply_apply] at this
      exact this
    rw [hb, Equiv.apply_symm_apply]
  · -- stable paths
    obtain ⟨Q₀, rfl⟩ := (iso.stablePathEquiv hG).surjective Q
    rw [hΞP]
    -- the incidence profiles agree
    have hinc : ∀ L, coreIncidence (tripodCore core s) L
        (φ'.ident.row (iso'.stablePathEquiv hG Q₀)) =
        coreIncidence (tripodCore core s) L (φ.ident.row (iso.stablePathEquiv hG Q₀)) := by
      intro L
      have e1 := φ.ident.incidence (φ.ident.vertex.symm L) (φ.ident.row (iso.stablePathEquiv hG Q₀))
      have e2 := φ'.ident.incidence (φ'.ident.vertex.symm L)
        (φ'.ident.row (iso'.stablePathEquiv hG Q₀))
      rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at e1 e2
      rw [← e1, ← e2, Ξ.incidenceCount_map hφc, hV, hΞP]
    rcases Dichotomy.isGSlot_or_eq_legSlot (φ.ident.row (iso.stablePathEquiv hG Q₀)) with
      hj | ⟨k, hk⟩
    · -- a G-slot: a glued old path, pinned by its merged label and its ends
      obtain ⟨z, hz⟩ := Onto.exists_gluedPath_eq_gSlot hD hT hπ hT0 iso
        (shapeLabels_of_gluedLabels hL) ⟨_, hj⟩
      have hQ₀ : Q₀ = CutPaths.gluedPath ψ.data π hD hT hπ z := by
        apply (iso.stablePathEquiv hG).injective
        rw [hz, Equiv.eq_symm_apply]
        exact Fin.ext rfl
      subst hQ₀
      have hm := pieceLabel_eq hπ iso hL z
      have hm' := pieceLabel_eq hπ iso' hL' z
      unfold pieceLabel at hm hm'
      rw [← GeometricDatumIso.stablePathEquiv_mk] at hm hm'
      have hmerge : mergeSlot s (φ'.ident.row (iso'.stablePathEquiv hG
          (CutPaths.gluedPath ψ.data π hD hT hπ z))) =
          mergeSlot s (φ.ident.row (iso.stablePathEquiv hG
            (CutPaths.gluedPath ψ.data π hD hT hπ z))) :=
        hm'.trans hm.symm
      set j := φ.ident.row (iso.stablePathEquiv hG (CutPaths.gluedPath ψ.data π hD hT hπ z))
        with hjdef
      set j' := φ'.ident.row (iso'.stablePathEquiv hG (CutPaths.gluedPath ψ.data π hD hT hπ z))
        with hj'def
      have hjc : j = Fin.castAdd 3 ⟨j.val, hj⟩ := Fin.ext rfl
      rcases Dichotomy.isGSlot_or_eq_legSlot j' with hj' | ⟨k', hk'⟩
      · have hj'c : j' = Fin.castAdd 3 ⟨j'.val, hj'⟩ := Fin.ext rfl
        have hsame : SameEnds (tripodCore core s) j' j := sameEnds_of_coreIncidence _ hinc
        rw [hjc, hj'c] at hsame
        rw [hjc, hj'c, mergeSlot_castAdd, mergeSlot_castAdd, Option.some_inj] at hmerge
        rw [hjc, hj'c, hdet _ _ hmerge (sameEnds_markedCore hsame)]
      · exfalso
        rw [hk', mergeSlot_legSlot, hjc, mergeSlot_castAdd] at hmerge
        exact absurd hmerge (by simp)
    · -- a leg, pinned by the clause `leg`
      obtain ⟨e₁, he₁, hr₁⟩ := hL.leg k
      obtain ⟨e₃, he₃, hr₃⟩ := hL'.leg k
      have he₁' : e₁ = iso.nonDanglingEdgeEquiv hG (Onto.legND (π := π) hD hT k) :=
        Subtype.ext he₁
      have he₃' : e₃ = iso'.nonDanglingEdgeEquiv hG (Onto.legND (π := π) hD hT k) :=
        Subtype.ext he₃
      have h1 : iso.stablePathEquiv hG Q₀ = e₁.stablePath :=
        φ.ident.row.injective (hk.trans hr₁.symm)
      rw [he₁', ← GeometricDatumIso.stablePathEquiv_mk] at h1
      have hQ := (iso.stablePathEquiv hG).injective h1
      subst hQ
      rw [hk, GeometricDatumIso.stablePathEquiv_mk, ← he₃', hr₃]

end SamePlacement

/-! ## 3. Moving a mark to another sheet of its source edge -/

section LeafSwap

variable {T T' : CFGraph} {d : ℕ} {D : GluingDatum T d} {D' : GluingDatum T' d}
  (Θ : GeometricDatumIso D D')

/-- `Θ` at `u`, followed by the transposition carrying the image of `a` to `a'`. -/
def armPerm (u : T.V) (a a' : Fin d) : Equiv.Perm (Fin d) :=
  (Θ.vertexPerm u).trans (Equiv.swap (Θ.vertexPerm u a) a')

theorem armPerm_apply_a (u : T.V) (a a' : Fin d) : armPerm Θ u a a' a = a' := by
  simp [armPerm]

theorem armPerm_apply_of_ne (u : T.V) (a a' b : Fin d) (h₁ : Θ.vertexPerm u b ≠ Θ.vertexPerm u a)
    (h₂ : Θ.vertexPerm u b ≠ a') : armPerm Θ u a a' b = Θ.vertexPerm u b := by
  simp only [armPerm, Equiv.trans_apply]
  exact Equiv.swap_apply_of_ne_of_ne h₁ h₂

/-- **`leafIso` with the sheet of the arm changed**: the arm at `u` glues `a` to `b`, its image
glues `a'` to `b'`; the arm and the tip are permuted by `armPerm`, which carries `a` to `a'`. The
hypothesis `hrel` is the compatibility at `u`: the transposition stays in the blocks of `u`. -/
def leafSwapIso (u : T.V) (u' : T'.V) (a b a' b' : Fin d) (hu : Θ.targetVertex u = u')
    (hb : armPerm Θ u a a' b = b')
    (hrel : ∀ i, (D.vertexPartition u).Rel ((Θ.vertexPerm u).symm (armPerm Θ u a a' i)) i) :
    GeometricDatumIso (leafDatum D u a b) (leafDatum D' u' a' b') where
  targetVertex := Equiv.sumCongr Θ.targetVertex (Equiv.refl Unit)
  targetEdge := (leafOcc T u).symm.trans ((Equiv.optionCongr Θ.targetEdge).trans (leafOcc T' u'))
  ends ε := by
    obtain ⟨o, rfl⟩ := (leafOcc T u).surjective ε
    cases o with
    | none =>
      left
      show ((leafOcc T' u' (Option.map Θ.targetEdge ((leafOcc T u).symm (leafOcc T u none))) :
        (leafTarget T' u').edges) : (leafTarget T' u').V × (leafTarget T' u').V) = _
      rw [Equiv.symm_apply_apply, Option.map_none, leafOcc_none, leafOcc_none, ← hu]
      rfl
    | some e =>
      show UnorderedEnds _ _ ((leafOcc T' u' (Option.map Θ.targetEdge ((leafOcc T u).symm
        (leafOcc T u (some e)))) : (leafTarget T' u').edges) :
          (leafTarget T' u').V × (leafTarget T' u').V)
      rw [Equiv.symm_apply_apply, Option.map_some, leafOcc_some, leafOcc_some]
      rcases Θ.ends e with h | h
      · left; rw [h]; rfl
      · right; rw [h]; rfl
  vertexPerm := Sum.elim Θ.vertexPerm fun _ ↦ armPerm Θ u a a'
  edgePerm ε := Option.elim ((leafOcc T u).symm ε) (armPerm Θ u a a') Θ.edgePerm
  vertexPartition v := by
    rcases v with w | ⟨⟩
    · exact Θ.vertexPartition w
    · show SheetOps.pair a' b' = (SheetOps.pair a b).relabel (armPerm Θ u a a')
      rw [pair_relabel, armPerm_apply_a, hb]
  edgePartition ε := by
    obtain ⟨o, rfl⟩ := (leafOcc T u).surjective ε
    cases o with
    | none =>
      show (leafDatum D' u' a' b').edgePartition (leafOcc T' u' (Option.map Θ.targetEdge
        ((leafOcc T u).symm (leafOcc T u none)))) = _
      rw [Equiv.symm_apply_apply, Option.map_none, leafDatum_edgePartition_none,
        leafDatum_edgePartition_none, SheetPartition.discrete_relabel]
    | some e =>
      show (leafDatum D' u' a' b').edgePartition (leafOcc T' u' (Option.map Θ.targetEdge
        ((leafOcc T u).symm (leafOcc T u (some e))))) = _
      rw [Equiv.symm_apply_apply, Option.map_some, leafDatum_edgePartition_some,
        leafDatum_edgePartition_some]
      simp only [Option.elim_some]
      exact Θ.edgePartition e
  compatible ε w hw i := by
    obtain ⟨o, rfl⟩ := (leafOcc T u).surjective ε
    cases o with
    | none =>
      rw [leafOcc_none] at hw
      simp only [Equiv.symm_apply_apply, Option.elim_none]
      rcases w with v | ⟨⟩
      · have hv : u = v := by
          rcases hw with h | h
          · exact leafOld_injective T u h
          · exact absurd h (by simp [leafTip])
        subst hv
        exact hrel i
      · show (SheetOps.pair a b).Rel ((armPerm Θ u a a').symm (armPerm Θ u a a' i)) i
        rw [Equiv.symm_apply_apply]
        exact rfl
    | some e =>
      rw [leafOcc_some] at hw
      simp only [Equiv.symm_apply_apply, Option.elim_some]
      rcases w with v | ⟨⟩
      · have hv : (e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v := by
          rcases hw with h | h
          · exact Or.inl (leafOld_injective T u h)
          · exact Or.inr (leafOld_injective T u h)
        exact Θ.compatible e v hv i
      · exfalso
        rcases hw with h | h <;> exact absurd h (by simp [leafOld])

variable (u : T.V) (u' : T'.V) (a b a' b' : Fin d) (hu : Θ.targetVertex u = u')
  (hb : armPerm Θ u a a' b = b')
  (hrel : ∀ i, (D.vertexPartition u).Rel ((Θ.vertexPerm u).symm (armPerm Θ u a a' i)) i)

theorem leafSwapIso_targetEdge_some (e : T.edges) :
    (leafSwapIso Θ u u' a b a' b' hu hb hrel).targetEdge (leafOcc T u (some e)) =
      leafOcc T' u' (some (Θ.targetEdge e)) := by
  show leafOcc T' u' (Option.map Θ.targetEdge ((leafOcc T u).symm (leafOcc T u (some e)))) = _
  rw [Equiv.symm_apply_apply, Option.map_some]

theorem leafSwapIso_targetEdge_none :
    (leafSwapIso Θ u u' a b a' b' hu hb hrel).targetEdge (leafOcc T u none) = leafOcc T' u' none := by
  show leafOcc T' u' (Option.map Θ.targetEdge ((leafOcc T u).symm (leafOcc T u none))) = _
  rw [Equiv.symm_apply_apply, Option.map_none]

theorem leafSwapIso_edgePerm_some (e : T.edges) :
    (leafSwapIso Θ u u' a b a' b' hu hb hrel).edgePerm (leafOcc T u (some e)) = Θ.edgePerm e := by
  show Option.elim ((leafOcc T u).symm (leafOcc T u (some e))) _ _ = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem leafSwapIso_edgePerm_none :
    (leafSwapIso Θ u u' a b a' b' hu hb hrel).edgePerm (leafOcc T u none) = armPerm Θ u a a' := by
  show Option.elim ((leafOcc T u).symm (leafOcc T u none)) _ _ = _
  rw [Equiv.symm_apply_apply]
  rfl

end LeafSwap

section SheetChange

variable {T : CFGraph} {d : ℕ}

/-- `π` with its sheets replaced by `σ`. -/
abbrev withSheet (π : Placement T d) (σ : Fin 3 → Fin d) : Placement T d :=
  ⟨π.edge₀, π.edge₁, π.edge₂, σ⟩

/-- The partition of `refine₃ D π` at mark `k` is that of the old edge under it. -/
theorem refine₃_vertexPartition_markVertex₃ (D : GluingDatum T d) (π : Placement T d)
    (k : Fin 3) :
    (refine₃ D π).vertexPartition (π.markVertex₃ k) = D.edgePartition (π.parentEdge k) := by
  match k with
  | 0 => rfl
  | 1 => exact refineDatum_edgePartition D π.edge₀ π.edge₁
  | 2 =>
    show (refineDatum (refineDatum D π.edge₀) π.edge₁).edgePartition π.edge₂ = _
    rw [refineDatum_edgePartition, refineDatum_edgePartition]
    rfl

variable (D : GluingDatum T d) (π : Placement T d) (σ : Fin 3 → Fin d)
  (hσ : ∀ k, (D.edgePartition (π.parentEdge k)).Rel (π.sheet k) (σ k))

/-- The identity of `extendDatum (refine₃ D π)`, read as an isomorphism onto the same datum for
`withSheet π σ` (the refined target and datum do not see the sheets). -/
def baseIso : GeometricDatumIso (extendDatum (refine₃ D π))
    (extendDatum (refine₃ D (withSheet π σ))) :=
  GeometricDatumIso.refl (extendDatum (refine₃ D π))

theorem baseIso_vertexPerm (v : π.T₃.V) : (baseIso D π σ).vertexPerm v = Equiv.refl _ := rfl

include hσ in
theorem rel_swap_castSucc (k : Fin 3) (i : Fin (d + 1)) :
    (SheetOps.extendNew ((refine₃ D π).vertexPartition (π.markVertex₃ k))).Rel
      (Equiv.swap (π.sheet k).castSucc (σ k).castSucc i) i := by
  rw [refine₃_vertexPartition_markVertex₃]
  have h := hσ k
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1
    exact (extendNew_rel_castSucc_iff _ _ _).mpr ⟨_, rfl, h.symm⟩
  · subst h2
    exact (extendNew_rel_castSucc_iff _ _ _).mpr ⟨_, rfl, h⟩
  · exact rfl

theorem armPerm_eq_swap {S S' : CFGraph} {E : GluingDatum S (d + 1)} {E' : GluingDatum S' (d + 1)}
    (Θ : GeometricDatumIso E E') (u : S.V) (hΘ : Θ.vertexPerm u = Equiv.refl _) (a a' : Fin (d + 1)) :
    armPerm Θ u a a' = Equiv.swap a a' := by
  unfold armPerm
  rw [hΘ]
  rfl

theorem swap_castSucc_last (a b : Fin d) :
    Equiv.swap a.castSucc b.castSucc (Fin.last d) = Fin.last d :=
  Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last _).ne' (Fin.castSucc_lt_last _).ne'

include hσ in
/-- Stage four: the arm at mark `0` moves to the sheet `σ 0`. -/
def sheetIso₄ : GeometricDatumIso
    (leafDatum (extendDatum (refine₃ D π)) (π.markVertex₃ 0) (π.sheet 0).castSucc (Fin.last d))
    (leafDatum (extendDatum (refine₃ D (withSheet π σ))) ((withSheet π σ).markVertex₃ 0)
      (σ 0).castSucc (Fin.last d)) :=
  leafSwapIso (baseIso D π σ) _ _ _ _ _ _ rfl
    (by rw [armPerm_eq_swap _ _ rfl, swap_castSucc_last])
    (fun i ↦ by
      rw [armPerm_eq_swap _ _ rfl]
      exact rel_swap_castSucc D π σ hσ 0 i)

theorem sheetIso₄_vertexPerm_inl (w : π.T₃.V) :
    (sheetIso₄ D π σ hσ).vertexPerm (Sum.inl w) = Equiv.refl _ := rfl

include hσ in
/-- Stage five: the arm at mark `1`. -/
def sheetIso₅ : GeometricDatumIso
    (leafDatum (leafDatum (extendDatum (refine₃ D π)) (π.markVertex₃ 0) (π.sheet 0).castSucc
      (Fin.last d)) (leafOld π.T₃ _ (π.markVertex₃ 1)) (π.sheet 1).castSucc (Fin.last d))
    (leafDatum (leafDatum (extendDatum (refine₃ D (withSheet π σ)))
      ((withSheet π σ).markVertex₃ 0) (σ 0).castSucc (Fin.last d))
      (leafOld (withSheet π σ).T₃ _ ((withSheet π σ).markVertex₃ 1)) (σ 1).castSucc
      (Fin.last d)) :=
  leafSwapIso (sheetIso₄ D π σ hσ) _ _ _ _ _ _ rfl
    (by rw [armPerm_eq_swap _ _ rfl, swap_castSucc_last])
    (fun i ↦ by
      rw [armPerm_eq_swap _ _ rfl]
      exact rel_swap_castSucc D π σ hσ 1 i)

include hσ in
/-- **The change of sheet** `glue(D, π) ≅ glue(D, withSheet π σ)`, when each new sheet `σ k` lies
in the block of `π.sheet k` over the old edge under mark `k`: the transposition of the two sheets
on the arm and at the tip, the identity elsewhere. -/
def sheetIso : GeometricDatumIso (glueDatum D π) (glueDatum D (withSheet π σ)) :=
  leafSwapIso (sheetIso₅ D π σ hσ) _ _ _ _ _ _ rfl
    (by rw [armPerm_eq_swap _ _ rfl, swap_castSucc_last])
    (fun i ↦ by
      rw [armPerm_eq_swap _ _ rfl]
      exact rel_swap_castSucc D π σ hσ 2 i)

theorem sheetIso_lift₃ (v : π.T₃.V) :
    (sheetIso D π σ hσ).targetVertex (π.lift₃ v) = (withSheet π σ).lift₃ v := rfl

theorem sheetIso_vertexPerm_lift₃ (v : π.T₃.V) :
    (sheetIso D π σ hσ).vertexPerm (π.lift₃ v) = Equiv.refl _ := rfl

theorem sheetIso_edgePerm_liftE₃ (ε : π.T₃.edges) :
    (sheetIso D π σ hσ).edgePerm (π.liftE₃ ε) = Equiv.refl _ := by
  refine (leafSwapIso_edgePerm_some (sheetIso₅ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_
  refine (leafSwapIso_edgePerm_some (sheetIso₄ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_
  exact leafSwapIso_edgePerm_some (baseIso D π σ) _ _ _ _ _ _ _ _ _ _

theorem sheetIso_liftE₃ (ε : π.T₃.edges) :
    (sheetIso D π σ hσ).targetEdge (π.liftE₃ ε) = (withSheet π σ).liftE₃ ε := by
  refine (leafSwapIso_targetEdge_some (sheetIso₅ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_
  refine congrArg (fun x ↦ leafOcc _ _ (some x))
    ((leafSwapIso_targetEdge_some (sheetIso₄ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_)
  exact congrArg (fun x ↦ leafOcc _ _ (some x))
    (leafSwapIso_targetEdge_some (baseIso D π σ) _ _ _ _ _ _ _ _ _ _)

theorem sheetIso_armEdge (k : Fin 3) :
    (sheetIso D π σ hσ).targetEdge (π.armEdge k) = (withSheet π σ).armEdge k ∧
      (sheetIso D π σ hσ).edgePerm (π.armEdge k) =
        Equiv.swap (π.sheet k).castSucc (σ k).castSucc := by
  match k with
  | 0 =>
    constructor
    · refine (leafSwapIso_targetEdge_some (sheetIso₅ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_
      refine congrArg (fun x ↦ leafOcc _ _ (some x))
        ((leafSwapIso_targetEdge_some (sheetIso₄ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_)
      exact congrArg (fun x ↦ leafOcc _ _ (some x))
        (leafSwapIso_targetEdge_none (baseIso D π σ) _ _ _ _ _ _ _ _ _)
    · refine (leafSwapIso_edgePerm_some (sheetIso₅ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_
      refine (leafSwapIso_edgePerm_some (sheetIso₄ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_
      refine (leafSwapIso_edgePerm_none (baseIso D π σ) _ _ _ _ _ _ _ _ _).trans ?_
      exact armPerm_eq_swap _ _ rfl _ _
  | 1 =>
    constructor
    · refine (leafSwapIso_targetEdge_some (sheetIso₅ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_
      exact congrArg (fun x ↦ leafOcc _ _ (some x))
        (leafSwapIso_targetEdge_none (sheetIso₄ D π σ hσ) _ _ _ _ _ _ _ _ _)
    · refine (leafSwapIso_edgePerm_some (sheetIso₅ D π σ hσ) _ _ _ _ _ _ _ _ _ _).trans ?_
      refine (leafSwapIso_edgePerm_none (sheetIso₄ D π σ hσ) _ _ _ _ _ _ _ _ _).trans ?_
      exact armPerm_eq_swap _ _ rfl _ _
  | 2 =>
    refine ⟨leafSwapIso_targetEdge_none (sheetIso₅ D π σ hσ) _ _ _ _ _ _ _ _ _, ?_⟩
    refine (leafSwapIso_edgePerm_none (sheetIso₅ D π σ hσ) _ _ _ _ _ _ _ _ _).trans ?_
    exact armPerm_eq_swap _ _ rfl _ _

theorem sheetIso_vertexPerm_last (v : π.T₆.V) :
    (sheetIso D π σ hσ).vertexPerm v (Fin.last d) = Fin.last d := by
  rcases π.T₆_vertex_cases v with ⟨w, rfl⟩ | ⟨k, rfl⟩
  · rw [sheetIso_vertexPerm_lift₃]; rfl
  · match k with
    | 0 =>
      show armPerm (baseIso D π σ) _ _ _ (Fin.last d) = _
      rw [armPerm_eq_swap _ _ rfl, swap_castSucc_last]
    | 1 =>
      show armPerm (sheetIso₄ D π σ hσ) _ _ _ (Fin.last d) = _
      rw [armPerm_eq_swap _ _ rfl, swap_castSucc_last]
    | 2 =>
      show armPerm (sheetIso₅ D π σ hσ) _ _ _ (Fin.last d) = _
      rw [armPerm_eq_swap _ _ rfl, swap_castSucc_last]

theorem sheetIso_oldSourceVertex (x : D.SourceVertex) :
    (sheetIso D π σ hσ).sourceVertexEquiv (π.oldSourceVertex D x) =
      (withSheet π σ).oldSourceVertex D x := by
  show (sheetIso D π σ hσ).sourceVertexEquiv
    ((glueDatum D π).sourceEndpoint (π.lift₃ _) x.1.2.castSucc) = _
  rw [sourceEndpoint_map, sheetIso_lift₃, sheetIso_vertexPerm_lift₃]
  rfl

theorem sheetIso_markSourceVertex (k : Fin 3) :
    (sheetIso D π σ hσ).sourceVertexEquiv (π.markSourceVertex D k) =
      (withSheet π σ).markSourceVertex D k := by
  show (sheetIso D π σ hσ).sourceVertexEquiv
    ((glueDatum D π).sourceEndpoint (π.lift₃ (π.markVertex₃ k)) (π.sheet k).castSucc) = _
  rw [sourceEndpoint_map, sheetIso_lift₃, sheetIso_vertexPerm_lift₃]
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show (SheetOps.extendNew ((refine₃ D π).vertexPartition (π.markVertex₃ k))).repr
      (π.sheet k).castSucc =
    (SheetOps.extendNew ((refine₃ D π).vertexPartition (π.markVertex₃ k))).repr (σ k).castSucc
  have h := rel_swap_castSucc D π σ hσ k (π.sheet k).castSucc
  rw [Equiv.swap_apply_left] at h
  exact h.symm

theorem sheetIso_oldSourceEdge (x : D.SourceEdge) :
    (sheetIso D π σ hσ).sourceEdgeEquiv (π.oldSourceEdge D x) =
      (withSheet π σ).oldSourceEdge D x := by
  show (sheetIso D π σ hσ).sourceEdgeEquiv
    ((glueDatum D π).sourceEdge (π.liftE₃ _) x.1.2.castSucc) = _
  rw [sourceEdge_map, sheetIso_liftE₃, sheetIso_edgePerm_liftE₃]
  rfl

theorem sheetIso_armSourceEdge (k : Fin 3) :
    (sheetIso D π σ hσ).sourceEdgeEquiv (π.armSourceEdge D k) =
      (withSheet π σ).armSourceEdge D k := by
  show (sheetIso D π σ hσ).sourceEdgeEquiv
    ((glueDatum D π).sourceEdge (π.armEdge k) (π.sheet k).castSucc) = _
  rw [sourceEdge_map, (sheetIso_armEdge D π σ hσ k).1, (sheetIso_armEdge D π σ hσ k).2,
    Equiv.swap_apply_left]
  rfl

theorem sheetIso_symm_last (x : (glueDatum D (withSheet π σ)).SourceVertex)
    (hx : x.1.2 = Fin.last d) :
    ((sheetIso D π σ hσ).sourceVertexEquiv.symm x).1.2 = Fin.last d := by
  set z := (sheetIso D π σ hσ).sourceVertexEquiv.symm x with hz
  have hzx : (sheetIso D π σ hσ).sourceVertexEquiv z = x := Equiv.apply_symm_apply _ _
  have h2 : (sheetIso D π σ hσ).vertexPerm z.1.1 z.1.2 = x.1.2 := by
    have := congrArg (fun w : (glueDatum D (withSheet π σ)).SourceVertex ↦ w.1.2) hzx
    exact this
  rw [hx, ← sheetIso_vertexPerm_last D π σ hσ z.1.1] at h2
  exact ((sheetIso D π σ hσ).vertexPerm z.1.1).injective h2

end SheetChange

section SheetLabels

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {d : ℕ} {yG : Fin p → ℚ}
  {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}

/-- **The glued labels move along a change of sheet.** -/
theorem gluedLabels_sheetIso {ψ : FibreMember core yG d} (π : Placement ψ.target d)
    (σ : Fin 3 → Fin d)
    (hσ : ∀ k, (ψ.data.edgePartition (π.parentEdge k)).Rel (π.sheet k) (σ k))
    {φ' : FibreMember (tripodCore core s) y (d + 1)}
    (iso' : GeometricDatumIso (glueDatum ψ.data (withSheet π σ)) φ'.data)
    (hL' : GluedLabels s ψ (withSheet π σ) φ'.ident iso') :
    GluedLabels s ψ π φ'.ident ((sheetIso ψ.data π σ hσ).trans iso') := by
  refine ⟨fun b ↦ ?_, fun k ↦ ?_, ?_, fun e ↦ ?_, fun k ↦ ?_⟩
  · rw [hL'.old b, trans_sourceVertexEquiv, sheetIso_oldSourceVertex]
  · rw [hL'.mark k, trans_sourceVertexEquiv, sheetIso_markSourceVertex]
  · have htr : ((sheetIso ψ.data π σ hσ).trans iso').sourceVertexEquiv.symm
        (φ'.ident.vertex.symm (centre n)).1 = (sheetIso ψ.data π σ hσ).sourceVertexEquiv.symm
          (iso'.sourceVertexEquiv.symm (φ'.ident.vertex.symm (centre n)).1) := by
      rw [Equiv.symm_apply_eq, trans_sourceVertexEquiv, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    rw [htr]
    exact sheetIso_symm_last ψ.data π σ hσ _ hL'.centre
  · obtain ⟨e', he', hr⟩ := hL'.row e
    exact ⟨e', by rw [he', trans_sourceEdgeEquiv, sheetIso_oldSourceEdge], hr⟩
  · obtain ⟨e', he', hr⟩ := hL'.leg k
    exact ⟨e', by rw [he', trans_sourceEdgeEquiv, sheetIso_armSourceEdge], hr⟩

end SheetLabels

/-! ## 4. The two remaining statements, and the assembly -/

section Assembly

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p}

/-- **The placement is forced** (§5.5, "Well defined"): when no
mark sits on a loop slot of `G̃`, two open gluings of one member `ψ` place the marks on the same
source edges, in the same order, so the placements differ only in the choice of a sheet in the
block of each mark's source edge. -/
theorem placement_forced (hloop : MarksOffLoops core s)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} {ψ : FibreMember core (baseRequest s y) (2 + 2)}
    {φ φ' : FibreMember (tripodCore core s) y (3 + 2)} (hφ : φ.Open) (hφ' : φ'.Open)
    {π π' : Placement ψ.target (2 + 2)} (hπ : π.NonDangling ψ.data)
    (hπ' : π'.NonDangling ψ.data)
    (iso : GeometricDatumIso (glueDatum ψ.data π) φ.data)
    (iso' : GeometricDatumIso (glueDatum ψ.data π') φ'.data)
    (hL : GluedLabels s ψ π φ.ident iso) (hL' : GluedLabels s ψ π' φ'.ident iso') :
    ∃ σ : Fin 3 → Fin (2 + 2), π' = withSheet π σ ∧
      ∀ k, (ψ.data.edgePartition (π.parentEdge k)).Rel (π.sheet k) (σ k) := by
  -- Each open gluing gives label data at the third stage with positive lengths
  -- (`Chains.labelData₃_of_gluing`), which merge back to the rows of `ψ` at its coordinates
  -- (`FibreMember.coords_unique`); a refinement of a layout with positive lengths is the
  -- forward one (`Chains.three_forced`, from `Chains.analyze`), so the three mark edges agree.
  exact Chains.placement_forced' hloop.1 hloop.2.1 hloop.2.2 hφ hφ' hπ hπ' iso iso' hL hL'

/-- **The placement is forced** (§5.5, "Well defined"): over a
loopless `G̃`, two open gluings of one member are isomorphic over `Γ̃`. Looplessness puts no mark
on a loop slot (`marksOffLoops_of_loopless`); the `TripodModel` core is loopless
(`TripodModel.loopless`), so this is all the assembly needs. -/
theorem nonempty_iso_of_isGluingOf_self (hloop : ∀ i, core.tail i ≠ core.head i)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    {ψ : FibreMember core (baseRequest s y) (2 + 2)}
    {φ φ' : FibreMember (tripodCore core s) y (3 + 2)} (hφ : φ.Open) (hφ' : φ'.Open)
    (h : IsGluingOf s ψ φ) (h' : IsGluingOf s ψ φ') : Nonempty (GeometricMemberIso φ φ') := by
  obtain ⟨π, hπ, iso, hL⟩ := h
  obtain ⟨π', hπ', iso', hL'⟩ := h'
  have hoff : MarksOffLoops core s := marksOffLoops_of_loopless hloop
  obtain ⟨σ, rfl, hσ⟩ := placement_forced hoff hφ hφ' hπ hπ' iso iso' hL hL'
  exact nonempty_iso_of_samePlacement hπ iso _ hL (gluedLabels_sheetIso π σ hσ iso' hL')
    (piecesDetermined_of_marksOffLoops hoff)

end Assembly

end WellDefined

end GenusSixExistence.Tripod.Gluing

end
