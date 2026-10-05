module

public import GenusSixExistence.BrillNoetherRank.Tripod.GluingRestrict
public import GenusSixExistence.BrillNoetherRank.Tripod.Dichotomy

@[expose] public section

/-!
# Injectivity of the gluing on classes

The proof of `GluingClasses.nonempty_iso_of_isGluingOf_iso`. Prose proof:
`Research/genus-six-brill-noether-rank.md`, §5.5 (The bijection, "Injective": deleting from
glue(ψ) the new sheet and the arms, and undoing the refinement at the marks, gives back ψ). This
direction needs no genericity. An isomorphism `φ ≅ φ'` over `Γ̃` of two gluings, read through the
two gluing isomorphisms, is an isomorphism `Ψ : glue(ψ, π) ≅ glue(ψ', π')` that

* carries mark `k` to mark `k` and the centre to the centre (the vertex clauses of
  `GluedLabels`);
* carries the arm of leg `k` in the sheet of mark `k` to its counterpart, because mark `k` meets
  leg `k` exactly once (`Dichotomy.legEdge_unique_at_mark`); hence the arms and the tips;
* carries the new sheet to the new sheet over all of `T₃` (`vertexPerm_last`: it does at the
  centre, and the new sheet is a singleton block over `T₃`).

So it restricts to the old sheets over `T₃` (`restrict₃`) and un-refines at the three marks
(`exists_unrefine₃`) to `R : ψ.data ≅ ψ'.data`. `R` is over `G̃`: on branch vertices by the clause
`old`, and on stable paths by the clause `row` together with `glued_row_piece`, which extends
`row` from the first piece of an old edge to every piece. That extension is the one place where
the marks matter: two pieces meeting at mark `k` lie on the two G-slots at `tripodMark n k`, and
these merge to one slot of `G̃` (`mergeSlot_eq_of_incident_mark`).
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

/-! ## The pieces of a G̃-slot at a mark merge to one slot -/

section Merge

variable {n p : ℕ}

theorem mergeOne_castSucc {q : ℕ} (e i : Fin q) : mergeOne e i.castSucc = i := by
  simp [mergeOne]

theorem mergeOne_last {q : ℕ} (e : Fin q) : mergeOne e (Fin.last q) = e := by
  simp [mergeOne]

/-- A slot of `subdivide C e` at an old vertex merges to a slot of `C` at that vertex. -/
theorem incident_mergeOne {m q : ℕ} (C : Core m q) (e : Fin q) (v : Fin m) (j : Fin (q + 1))
    (h : (subdivide C e).tail j = v.castSucc ∨ (subdivide C e).head j = v.castSucc) :
    C.tail (mergeOne e j) = v ∨ C.head (mergeOne e j) = v := by
  induction j using Fin.lastCases with
  | last =>
    rw [subdivide_tail_last, subdivide_head_last] at h
    rw [mergeOne_last]
    rcases h with h | h
    · exact absurd h (Fin.castSucc_lt_last v).ne'
    · exact Or.inr (Fin.castSucc_injective _ h)
  | cast i =>
    rw [subdivide_tail_castSucc, subdivide_head_castSucc] at h
    rw [mergeOne_castSucc]
    rcases h with h | h
    · exact Or.inl (Fin.castSucc_injective _ h)
    · split_ifs at h with hie
      · exact absurd h (Fin.castSucc_lt_last v).ne'
      · exact Or.inr (Fin.castSucc_injective _ h)

/-- Both slots at the new vertex of `subdivide C e` merge to `e`. -/
theorem mergeOne_of_incident_last {m q : ℕ} (C : Core m q) (e : Fin q) (j : Fin (q + 1))
    (h : (subdivide C e).tail j = Fin.last m ∨ (subdivide C e).head j = Fin.last m) :
    mergeOne e j = e := by
  induction j using Fin.lastCases with
  | last => exact mergeOne_last e
  | cast i =>
    rw [subdivide_tail_castSucc, subdivide_head_castSucc] at h
    rw [mergeOne_castSucc]
    rcases h with h | h
    · exact absurd h (Fin.castSucc_lt_last _).ne
    · split_ifs at h with hie
      · exact hie
      · exact absurd h (Fin.castSucc_lt_last _).ne

/-- **The two slots of the marked core at mark `k` merge to one slot of `G̃`.** -/
theorem merge_eq_of_incident_mark (core : Core n p) (s : MarkSlots p) (k : Fin 3)
    {i₁ i₂ : Fin (p + 1 + 1 + 1)}
    (h₁ : (markedCore core s).tail i₁ = markVertex n k ∨
      (markedCore core s).head i₁ = markVertex n k)
    (h₂ : (markedCore core s).tail i₂ = markVertex n k ∨
      (markedCore core s).head i₂ = markVertex n k) :
    mergeOne s.first (mergeOne s.second (mergeOne s.third i₁)) =
      mergeOne s.first (mergeOne s.second (mergeOne s.third i₂)) := by
  unfold markedCore at h₁ h₂
  match k with
  | 0 =>
    have hv : markVertex n 0 = (Fin.last n).castSucc.castSucc := Fin.ext (by simp [markVertex])
    rw [hv] at h₁ h₂
    rw [mergeOne_of_incident_last _ _ _ (incident_mergeOne _ _ _ _ (incident_mergeOne _ _ _ _ h₁)),
      mergeOne_of_incident_last _ _ _ (incident_mergeOne _ _ _ _ (incident_mergeOne _ _ _ _ h₂))]
  | 1 =>
    have hv : markVertex n 1 = (Fin.last (n + 1)).castSucc := Fin.ext (by simp [markVertex])
    rw [hv] at h₁ h₂
    rw [mergeOne_of_incident_last _ _ _ (incident_mergeOne _ _ _ _ h₁),
      mergeOne_of_incident_last _ _ _ (incident_mergeOne _ _ _ _ h₂)]
  | 2 =>
    have hv : markVertex n 2 = Fin.last (n + 1 + 1) := Fin.ext (by simp [markVertex])
    rw [hv] at h₁ h₂
    rw [mergeOne_of_incident_last _ _ _ h₁, mergeOne_of_incident_last _ _ _ h₂]

theorem mergeSlot_castAdd (s : MarkSlots p) (i : Fin (p + 1 + 1 + 1)) :
    mergeSlot s (Fin.castAdd 3 i) =
      some (mergeOne s.first (mergeOne s.second (mergeOne s.third i))) := by
  unfold mergeSlot
  rw [dite_eq_left (by simp only [Fin.val_castAdd]; exact i.isLt)]
  rfl

/-- **The slots of `Γ̃` at mark `k` other than leg `k` merge to one slot of `G̃`.** -/
theorem mergeSlot_eq_of_incident_mark (core : Core n p) (s : MarkSlots p) (k : Fin 3)
    {j₁ j₂ : Fin (p + 1 + 1 + 1 + 3)}
    (h₁ : (tripodCore core s).tail j₁ = tripodMark n k ∨ (tripodCore core s).head j₁ = tripodMark n k)
    (h₂ : (tripodCore core s).tail j₂ = tripodMark n k ∨ (tripodCore core s).head j₂ = tripodMark n k)
    (hj₁ : j₁ ≠ legSlot p k) (hj₂ : j₂ ≠ legSlot p k) :
    mergeSlot s j₁ = mergeSlot s j₂ := by
  have hG : ∀ {j : Fin (p + 1 + 1 + 1 + 3)},
      ((tripodCore core s).tail j = tripodMark n k ∨ (tripodCore core s).head j = tripodMark n k) →
      j ≠ legSlot p k → ∃ i, j = Fin.castAdd 3 i ∧
        ((markedCore core s).tail i = markVertex n k ∨ (markedCore core s).head i = markVertex n k) := by
    intro j hj hjl
    rcases Dichotomy.isGSlot_or_eq_legSlot j with hJ | ⟨k', rfl⟩
    · refine ⟨⟨j.val, hJ⟩, Fin.ext rfl, ?_⟩
      have hj' : j = Fin.castAdd 3 ⟨j.val, hJ⟩ := Fin.ext rfl
      rw [hj', Dichotomy.tripodCore_tail_castAdd, Dichotomy.tripodCore_head_castAdd] at hj
      rcases hj with h | h
      · exact Or.inl (Fin.castSucc_injective _ h)
      · exact Or.inr (Fin.castSucc_injective _ h)
    · exfalso
      rw [Dichotomy.tripodCore_tail_legSlot, Dichotomy.tripodCore_head_legSlot] at hj
      rcases hj with h | h
      · exact Dichotomy.centre_ne_tripodMark k h
      · exact hjl (by rw [Dichotomy.tripodMark_injective h])
  obtain ⟨i₁, rfl, hi₁⟩ := hG h₁ hj₁
  obtain ⟨i₂, rfl, hi₂⟩ := hG h₂ hj₂
  rw [mergeSlot_castAdd, mergeSlot_castAdd, merge_eq_of_incident_mark core s k hi₁ hi₂]

theorem oldLabel_injective : Function.Injective (oldLabel (n := n)) := fun _ _ h ↦
  Fin.castSucc_injective _ (Fin.castSucc_injective _ (Fin.castSucc_injective _
    (Fin.castSucc_injective _ h)))

end Merge

/-! ## Stable paths of a refinement, through the parents -/

section Pieces

variable {T : CFGraph} {d : ℕ}

/-- **The stable path of a refinement is that of its parent**: surviving edges whose parents lie on
one stable path of `D` lie on one stable path of `refineDatum D t`. -/
theorem Refine.stablePath_eq_of_parentND (D : GluingDatum T d) (t : T.edges) (hD : D.Connected)
    (y y' : NonDanglingEdge (refineDatum D t))
    (h : (Refine.parentND D t hD y).stablePath = (Refine.parentND D t hD y').stablePath) :
    y.stablePath = y'.stablePath := by
  classical
  let Q : NonDanglingEdge D → Prop := fun f ↦ ∀ y'' : NonDanglingEdge (refineDatum D t),
    Refine.parentSE D t y''.1 = f.1 → y''.stablePath = y.stablePath
  have hQ0 : Q (Refine.parentND D t hD y) := fun y'' h ↦ Refine.stablePath_eq_of_parentSE_eq D t hD h
  have hsurv : ∀ (x : D.SourceVertex) (f : NonDanglingEdge D),
      ¬ IsDangling (refineDatum D t) (Refine.piece D t x f.1) := fun x f ↦
    (Refine.isDangling_iff D t hD _).not.mpr (by rw [Refine.parentSE_piece]; exact f.2)
  have hclosed : ∀ a b : NonDanglingEdge D, Consecutive D a b → Q a → Q b := by
    rintro a b ⟨hab, x, ha, hb, hx⟩ hQa y'' hy''
    have hcons : Consecutive (refineDatum D t) ⟨_, hsurv x a⟩ ⟨_, hsurv x b⟩ := by
      refine ⟨fun h ↦ hab ?_, Refine.oldSV D t x, Refine.incident_piece D t ha,
        Refine.incident_piece D t hb, ?_⟩
      · have := congrArg (fun z : NonDanglingEdge (refineDatum D t) ↦ Refine.parentSE D t z.1) h
        simp only [Refine.parentSE_piece] at this
        exact Subtype.ext this
      · rw [Refine.nonDanglingValency_oldSV D t hD]; exact hx
    rw [Refine.stablePath_eq_of_parentSE_eq D t hD (y' := ⟨_, hsurv x b⟩)
        (by rw [hy'', Refine.parentSE_piece]),
      ← stablePath_eq_of_consecutive hcons]
    exact hQa _ (Refine.parentSE_piece D t x a.1)
  have hQ' : Q (Refine.parentND D t hD y') :=
    (eqvGen_iff_of_closed hclosed ((stablePath_eq_iff _ _).mp h)).mp hQ0
  exact (hQ' y' rfl).symm

theorem isDangling_iff₃ (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected)
    (y : (refine₃ D π).SourceEdge) :
    IsDangling (refine₃ D π) y ↔ IsDangling D (parentSE₃ D π y) := by
  unfold parentSE₃
  rw [Refine.isDangling_iff _ π.edge₂ (π.refine₂_connected D hD),
    Refine.isDangling_iff _ π.edge₁ (π.refine₁_connected D hD), Refine.isDangling_iff D π.edge₀ hD]

/-- Surviving edges of `refine₃ D π` with one parent in `D` lie on one stable path. -/
theorem stablePath_eq_of_parentSE₃_eq (D : GluingDatum T d) (π : Placement T d)
    (hD : D.Connected) (y y' : NonDanglingEdge (refine₃ D π))
    (h : parentSE₃ D π y.1 = parentSE₃ D π y'.1) : y.stablePath = y'.stablePath := by
  have hD₁ := π.refine₁_connected D hD
  have hD₂ := π.refine₂_connected D hD
  apply Refine.stablePath_eq_of_parentND _ π.edge₂ hD₂
  apply Refine.stablePath_eq_of_parentND _ π.edge₁ hD₁
  apply Refine.stablePath_eq_of_parentND D π.edge₀ hD
  exact congrArg NonDanglingEdge.stablePath (Subtype.ext h)

/-- The first piece of an old source edge, in `refine₃ D π`. -/
def firstPiece₃ (D : GluingDatum T d) (π : Placement T d) (x : D.SourceEdge) :
    (refine₃ D π).SourceEdge :=
  ⟨(subdivOcc _ π.edge₂ (some (subdivOcc _ π.edge₁ (some (subdivOcc T π.edge₀ (some x.1.1))))),
    x.1.2), by
    rw [refineDatum_edgePartition_some, refineDatum_edgePartition_some,
      refineDatum_edgePartition_some]
    exact x.2⟩

theorem parentSE₃_firstPiece₃ (D : GluingDatum T d) (π : Placement T d) (x : D.SourceEdge) :
    parentSE₃ D π (firstPiece₃ D π x) = x := by
  apply Subtype.ext
  show (parentT π.edge₀ (parentT π.edge₁ (parentT π.edge₂ (subdivOcc _ π.edge₂
    (some (subdivOcc _ π.edge₁ (some (subdivOcc T π.edge₀ (some x.1.1)))))))), x.1.2) = x.1
  rw [parentT_some, parentT_some, parentT_some]

theorem liftSE_firstPiece₃ (D : GluingDatum T d) (π : Placement T d) (x : D.SourceEdge) :
    liftSE D π (firstPiece₃ D π x) = π.oldSourceEdge D x := by
  apply Subtype.ext
  show (π.liftE₃ (firstPiece₃ D π x).1.1, x.1.2.castSucc) =
    (π.liftE₃ (subdivOcc _ π.edge₂ (some (subdivOcc _ π.edge₁ (some (subdivOcc T π.edge₀
      (some x.1.1)))))), ((glueDatum D π).edgePartition (π.liftE₃ (subdivOcc _ π.edge₂
        (some (subdivOcc _ π.edge₁ (some (subdivOcc T π.edge₀ (some x.1.1)))))))).repr
          x.1.2.castSucc)
  rw [glueDatum_edgePartition_liftE₃, SheetOps.extendNew_repr_castSucc,
    refineDatum_edgePartition_some, refineDatum_edgePartition_some,
    refineDatum_edgePartition_some, x.2]
  rfl

theorem oldSourceVertex_eq (D : GluingDatum T d) (π : Placement T d) (x : D.SourceVertex) :
    π.oldSourceVertex D x = oldVertex₃ D π (oldSV₃ D π x) := rfl

theorem markSourceVertex_eq (D : GluingDatum T d) (π : Placement T d) (k : Fin 3) :
    π.markSourceVertex D k = oldVertex₃ D π (markR₃ D π k) := by
  apply Subtype.ext
  rw [oldVertex₃_val]
  show (π.markTarget k,
    ((glueDatum D π).vertexPartition (π.markTarget k)).repr (π.sheet k).castSucc) = _
  rw [Placement.markTarget_eq_lift₃, glueDatum_vertexPartition_lift₃,
    SheetOps.extendNew_repr_castSucc]
  rfl

theorem armSourceEdge_incident (D : GluingDatum T d) (π : Placement T d) (k : Fin 3) :
    Incident (glueDatum D π) (π.armSourceEdge D k) (π.markSourceVertex D k) := by
  left
  refine (sourceEnds_sourceEdge_fst _ _ _).trans ?_
  exact congrArg (fun v ↦ (glueDatum D π).sourceEndpoint v (π.sheet k).castSucc)
    (congrArg Prod.fst (π.armEdge_ends k))

end Pieces

/-! ## The glued labels of every piece -/

section Labels

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {d : ℕ} {yG : Fin p → ℚ}
  {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {ψ : FibreMember core yG d} {π : Placement ψ.target d}
  {φ : FibreMember (tripodCore core s) y (d + 1)}

/-- The glued copy of a surviving edge of `refine₃ ψ.data π`. -/
def gluedND (hπ : π.NonDangling ψ.data) (z : NonDanglingEdge (refine₃ ψ.data π)) :
    NonDanglingEdge (glueDatum ψ.data π) :=
  ⟨liftSE ψ.data π z.1, (isDangling_liftSE_iff ψ.data π ψ.fullDim.valid.1
    ψ.fullDim.targetConnected hπ z.1).not.mpr z.2⟩

/-- The surviving parent in `ψ` of a surviving edge of `refine₃ ψ.data π`. -/
def parentND₃ (z : NonDanglingEdge (refine₃ ψ.data π)) : NonDanglingEdge ψ.data :=
  ⟨parentSE₃ ψ.data π z.1, (isDangling_iff₃ ψ.data π ψ.fullDim.valid.1 z.1).not.mp z.2⟩

variable (hπ : π.NonDangling ψ.data) (iso : GeometricDatumIso (glueDatum ψ.data π) φ.data)
  (hL : GluedLabels s ψ π φ.ident iso)

/-- The merged label of the glued copy of a surviving edge. -/
def pieceLabel (z : NonDanglingEdge (refine₃ ψ.data π)) : Option (Fin p) :=
  mergeSlot s (φ.ident.row (iso.nonDanglingEdgeEquiv
    (glueDatum_connected ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected)
      (gluedND hπ z)).stablePath)

include hL in
/-- **The merged label is constant along the stable paths of `refine₃ ψ.data π`.** Through a
vertex that is not a mark the two glued copies are consecutive; at mark `k` they lie on the two
G-slots there, which merge to one slot of `G̃`. -/
theorem pieceLabel_eq_of_consecutive {z₁ z₂ : NonDanglingEdge (refine₃ ψ.data π)}
    (h : Consecutive (refine₃ ψ.data π) z₁ z₂) :
    pieceLabel hπ iso z₁ = pieceLabel hπ iso z₂ := by
  obtain ⟨hne, x, hx₁, hx₂, hval⟩ := h
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hGc := glueDatum_connected ψ.data π hD hT
  have hv := nonDanglingValency_oldVertex₃ ψ.data π hD hT hπ x
  by_cases hm : ∃ k, x = markR₃ ψ.data π k
  · obtain ⟨k, rfl⟩ := hm
    have key : ∀ z : NonDanglingEdge (refine₃ ψ.data π),
        Incident (refine₃ ψ.data π) z.1 (markR₃ ψ.data π k) →
        ((tripodCore core s).tail (φ.ident.row (iso.nonDanglingEdgeEquiv hGc
            (gluedND hπ z)).stablePath) = tripodMark n k ∨
          (tripodCore core s).head (φ.ident.row (iso.nonDanglingEdgeEquiv hGc
            (gluedND hπ z)).stablePath) = tripodMark n k) ∧
        φ.ident.row (iso.nonDanglingEdgeEquiv hGc (gluedND hπ z)).stablePath ≠ legSlot p k := by
      intro z hz
      have hinc : Incident φ.data (iso.nonDanglingEdgeEquiv hGc (gluedND hπ z)).1
          (φ.ident.vertex.symm (tripodMark n k)).1 := by
        rw [hL.mark k, markSourceVertex_eq]
        exact (iso.incident_map_iff _ _).mpr ((incident_liftSE_oldVertex₃ _ _ _ _).mpr hz)
      refine ⟨Dichotomy.end_of_incident_vertex (Frame.of φ) (tripodMark n k) _ hinc,
        fun hleg ↦ ?_⟩
      obtain ⟨e₁, he₁, hr₁⟩ := hL.leg k
      have hinc₁ : Incident φ.data e₁.1 (φ.ident.vertex.symm (tripodMark n k)).1 := by
        rw [he₁, hL.mark k]
        exact (iso.incident_map_iff _ _).mpr (armSourceEdge_incident _ _ k)
      have heq := Dichotomy.legEdge_unique_at_mark (Frame.of φ) k hinc hinc₁ hleg hr₁
      have h' : liftSE ψ.data π z.1 = π.armSourceEdge ψ.data k := by
        apply iso.sourceEdgeEquiv.injective
        rw [← he₁]
        exact congrArg Subtype.val heq
      exact liftSE_ne_arm ψ.data π z.1 k (π.sheet k).castSucc h'
    obtain ⟨a₁, b₁⟩ := key z₁ hx₁
    obtain ⟨a₂, b₂⟩ := key z₂ hx₂
    exact mergeSlot_eq_of_incident_mark core s k a₁ a₂ b₁ b₂
  · push Not at hm
    have hsum : (∑ k : Fin 3, if x = markR₃ ψ.data π k then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun k _ ↦ ite_eq_right (hm k)
    rw [hsum, hval] at hv
    have hcons : Consecutive (glueDatum ψ.data π) (gluedND hπ z₁) (gluedND hπ z₂) :=
      ⟨fun h ↦ hne (Subtype.ext (liftSE_injective _ _ (congrArg Subtype.val h))), _,
        (incident_liftSE_oldVertex₃ _ _ _ _).mpr hx₁,
        (incident_liftSE_oldVertex₃ _ _ _ _).mpr hx₂, hv⟩
    unfold pieceLabel
    rw [← iso.stablePathEquiv_mk, ← iso.stablePathEquiv_mk, stablePath_eq_of_consecutive hcons]

include hL in
/-- **Every piece of an old edge carries its glued label** (the row list of §5.3): the glued
copy of a surviving edge of `refine₃ ψ.data π` lies on a slot of `Γ̃` merging to the slot of its
parent. The clause `row` of `GluedLabels` is the case of a first piece. -/
theorem pieceLabel_eq (z : NonDanglingEdge (refine₃ ψ.data π)) :
    pieceLabel hπ iso z = some (ψ.ident.row (parentND₃ z).stablePath) := by
  have hD := ψ.fullDim.valid.1
  set e := parentND₃ z with he
  let z₀ : NonDanglingEdge (refine₃ ψ.data π) := ⟨firstPiece₃ ψ.data π e.1, by
    rw [isDangling_iff₃ ψ.data π hD, parentSE₃_firstPiece₃]; exact e.2⟩
  have hpath : z.stablePath = z₀.stablePath :=
    stablePath_eq_of_parentSE₃_eq ψ.data π hD z z₀ (by
      show parentSE₃ ψ.data π z.1 = parentSE₃ ψ.data π (firstPiece₃ ψ.data π e.1)
      rw [parentSE₃_firstPiece₃, he]
      rfl)
  let Λ : StablePath (refine₃ ψ.data π) → Option (Fin p) :=
    Quot.lift (pieceLabel hπ iso) fun _ _ h ↦ pieceLabel_eq_of_consecutive hπ iso hL h
  have hz : pieceLabel hπ iso z = pieceLabel hπ iso z₀ := congrArg Λ hpath
  rw [hz]
  obtain ⟨e', he', hrow⟩ := hL.row e
  have hz₀ : iso.nonDanglingEdgeEquiv
      (glueDatum_connected ψ.data π hD ψ.fullDim.targetConnected) (gluedND hπ z₀) = e' := by
    apply Subtype.ext
    rw [he', GeometricDatumIso.nonDanglingEdgeEquiv_val]
    exact congrArg iso.sourceEdgeEquiv (liftSE_firstPiece₃ ψ.data π e.1)
  unfold pieceLabel
  rw [hz₀, hrow]

end Labels

/-! ## Injectivity -/

section Injective

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {d : ℕ} {yG : Fin p → ℚ}
  {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}

/-- **Two gluings that are isomorphic over `Γ̃` glue isomorphic members over `G̃`** (§5.5,
injectivity). No openness or genericity is used. -/
theorem nonempty_memberIso_of_glued {ψ ψ' : FibreMember core yG d}
    {π : Placement ψ.target d} {π' : Placement ψ'.target d}
    {φ φ' : FibreMember (tripodCore core s) y (d + 1)}
    (hπ : π.NonDangling ψ.data) (hπ' : π'.NonDangling ψ'.data)
    (iso : GeometricDatumIso (glueDatum ψ.data π) φ.data)
    (iso' : GeometricDatumIso (glueDatum ψ'.data π') φ'.data)
    (hL : GluedLabels s ψ π φ.ident iso) (hL' : GluedLabels s ψ' π' φ'.ident iso')
    (m : GeometricMemberIso φ φ') : Nonempty (GeometricMemberIso ψ ψ') := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  set Ψ : GeometricDatumIso (glueDatum ψ.data π) (glueDatum ψ'.data π') :=
    iso.trans (m.datum.trans iso'.symm) with hΨ
  have hΨV : ∀ a, iso'.sourceVertexEquiv (Ψ.sourceVertexEquiv a) =
      m.datum.sourceVertexEquiv (iso.sourceVertexEquiv a) := fun a ↦ by
    show iso'.sourceVertexEquiv (iso'.sourceVertexEquiv.symm
      (m.datum.sourceVertexEquiv (iso.sourceVertexEquiv a))) = _
    exact Equiv.apply_symm_apply _ _
  have hΨE : ∀ a, iso'.sourceEdgeEquiv (Ψ.sourceEdgeEquiv a) =
      m.datum.sourceEdgeEquiv (iso.sourceEdgeEquiv a) := fun a ↦ by
    show iso'.sourceEdgeEquiv (iso'.sourceEdgeEquiv.symm
      (m.datum.sourceEdgeEquiv (iso.sourceEdgeEquiv a))) = _
    exact Equiv.apply_symm_apply _ _
  -- the vertex labels move along `m`
  have hlabel : ∀ v : Fin (n + 1 + 1 + 1 + 1), (φ'.ident.vertex.symm v).1 =
      m.datum.sourceVertexEquiv (φ.ident.vertex.symm v).1 := fun v ↦ by
    rw [ident_vertex_symm_of_iso m v]; rfl
  have hlab : ∀ (v : Fin (n + 1 + 1 + 1 + 1)) a a',
      (φ.ident.vertex.symm v).1 = iso.sourceVertexEquiv a →
      (φ'.ident.vertex.symm v).1 = iso'.sourceVertexEquiv a' → Ψ.sourceVertexEquiv a = a' := by
    intro v a a' h h'
    apply iso'.sourceVertexEquiv.injective
    rw [hΨV, ← h, ← h', hlabel]
  -- the marks
  have hmarkS : ∀ k, Ψ.sourceVertexEquiv (π.markSourceVertex ψ.data k) =
      π'.markSourceVertex ψ'.data k := fun k ↦ hlab _ _ _ (hL.mark k) (hL'.mark k)
  have hmarkT : ∀ k, Ψ.targetVertex (π.markTarget k) = π'.markTarget k := fun k ↦
    congrArg (fun z : (glueDatum ψ'.data π').SourceVertex ↦ z.1.1) (hmarkS k)
  -- the arms: mark `k` meets leg `k` once
  have harmS : ∀ k, Ψ.sourceEdgeEquiv (π.armSourceEdge ψ.data k) =
      π'.armSourceEdge ψ'.data k := by
    intro k
    obtain ⟨e₁, he₁, hr₁⟩ := hL.leg k
    obtain ⟨e₃, he₃, hr₃⟩ := hL'.leg k
    have hr₂ : φ'.ident.row (m.datum.nonDanglingEdgeEquiv φ.fullDim.valid.1 e₁).stablePath =
        legSlot p k := (row_of_iso m e₁).trans hr₁
    have hi₃ : Incident φ'.data e₃.1 (φ'.ident.vertex.symm (tripodMark n k)).1 := by
      rw [he₃, hL'.mark k]
      exact (iso'.incident_map_iff _ _).mpr (armSourceEdge_incident _ _ k)
    have hi₂ : Incident φ'.data (m.datum.nonDanglingEdgeEquiv φ.fullDim.valid.1 e₁).1
        (φ'.ident.vertex.symm (tripodMark n k)).1 := by
      rw [hlabel, GeometricDatumIso.nonDanglingEdgeEquiv_val, m.datum.incident_map_iff, he₁,
        hL.mark k]
      exact (iso.incident_map_iff _ _).mpr (armSourceEdge_incident _ _ k)
    have heq := Dichotomy.legEdge_unique_at_mark (Frame.of φ') k hi₂ hi₃ hr₂ hr₃
    apply iso'.sourceEdgeEquiv.injective
    rw [hΨE, ← he₁, ← he₃]
    exact congrArg Subtype.val heq
  have harm : ∀ k, Ψ.targetEdge (π.armEdge k) = π'.armEdge k := fun k ↦
    congrArg (fun z : (glueDatum ψ'.data π').SourceEdge ↦ z.1.1) (harmS k)
  have htip : ∀ k, Ψ.targetVertex (π.tipTarget k) = π'.tipTarget k := by
    intro k
    have h := Ψ.ends (π.armEdge k)
    rw [harm, π.armEdge_ends, π'.armEdge_ends] at h
    rcases h with h | h
    · exact (congrArg Prod.snd h : π'.tipTarget k = Ψ.targetVertex (π.tipTarget k)).symm
    · exfalso
      have h2 : π'.tipTarget k = Ψ.targetVertex (π.markTarget k) := congrArg Prod.snd h
      rw [hmarkT] at h2
      exact π'.markTarget_ne_tipTarget k h2.symm
  -- the centre, in the new sheet
  set c := iso.sourceVertexEquiv.symm (φ.ident.vertex.symm (centre n)).1 with hcdef
  have hcc : Ψ.sourceVertexEquiv c =
      iso'.sourceVertexEquiv.symm (φ'.ident.vertex.symm (centre n)).1 :=
    hlab (centre n) _ _ (by rw [hcdef, Equiv.apply_symm_apply])
      (by rw [Equiv.apply_symm_apply])
  have hc : c.1.2 = Fin.last d := hL.centre
  have hc' : (Ψ.sourceVertexEquiv c).1.2 = Fin.last d := by rw [hcc]; exact hL'.centre
  have hnew := vertexPerm_last Ψ hT c hc hc'
  -- restrict to the old sheets, and un-refine at the marks
  set Θ := restrict₃ Ψ htip harm hnew with hΘ
  have hmark₃ : ∀ k, Θ.targetVertex (π.markVertex₃ k) = π'.markVertex₃ k := by
    intro k
    apply π'.lift₃_injective
    rw [← restrict₃_lift₃ Ψ htip harm hnew]
    exact hmarkT k
  obtain ⟨R, hRV, hRE⟩ := exists_unrefine₃ Θ hmark₃
  refine ⟨⟨R, fun b ↦ ?_, fun P ↦ ?_⟩⟩
  · -- over `G̃` on branch vertices: the clause `old`
    set b' := R.branchVertexEquiv hD b with hb'
    have h₁ := hL.old b
    have h₂ := hL'.old b'
    have hOld : Ψ.sourceVertexEquiv (π.oldSourceVertex ψ.data b.1) =
        π'.oldSourceVertex ψ'.data b'.1 := by
      rw [oldSourceVertex_eq, oldSourceVertex_eq, restrict₃_oldVertex₃ Ψ htip harm hnew, hRV]
      rfl
    have hEq : φ'.ident.vertex.symm (oldLabel (ψ.ident.vertex b)) =
        φ'.ident.vertex.symm (oldLabel (ψ'.ident.vertex b')) := by
      apply Subtype.ext
      rw [hlabel, h₁, ← hΨV, hOld, h₂]
    exact (oldLabel_injective (φ'.ident.vertex.symm.injective hEq)).symm
  · -- over `G̃` on stable paths: the clause `row`, extended to every piece
    obtain ⟨e, rfl⟩ := Quot.exists_rep P
    show ψ'.ident.row (R.stablePathEquiv hD e.stablePath) = ψ.ident.row e.stablePath
    rw [R.stablePathEquiv_mk hD e]
    have hΘc := π.refine₃_connected ψ.data hD
    let z₀ : NonDanglingEdge (refine₃ ψ.data π) := ⟨firstPiece₃ ψ.data π e.1, by
      rw [isDangling_iff₃ ψ.data π hD, parentSE₃_firstPiece₃]; exact e.2⟩
    let z' : NonDanglingEdge (refine₃ ψ'.data π') := Θ.nonDanglingEdgeEquiv hΘc z₀
    have hpar : parentND₃ z' = R.nonDanglingEdgeEquiv hD e := by
      apply Subtype.ext
      show parentSE₃ ψ'.data π' (Θ.sourceEdgeEquiv z₀.1) = R.sourceEdgeEquiv e.1
      rw [hRE, parentSE₃_firstPiece₃]
    have h' := pieceLabel_eq hπ' iso' hL' z'
    rw [hpar] at h'
    have hgl : iso'.nonDanglingEdgeEquiv
        (glueDatum_connected ψ'.data π' ψ'.fullDim.valid.1 ψ'.fullDim.targetConnected)
          (gluedND hπ' z') =
        m.datum.nonDanglingEdgeEquiv φ.fullDim.valid.1 (iso.nonDanglingEdgeEquiv
          (glueDatum_connected ψ.data π hD hT) (gluedND hπ z₀)) := by
      apply Subtype.ext
      show iso'.sourceEdgeEquiv (liftSE ψ'.data π' (Θ.sourceEdgeEquiv z₀.1)) =
        m.datum.sourceEdgeEquiv (iso.sourceEdgeEquiv (liftSE ψ.data π z₀.1))
      rw [← restrict₃_liftSE Ψ htip harm hnew, hΨE]
    have h₀ := pieceLabel_eq hπ iso hL z₀
    unfold pieceLabel at h' h₀
    rw [hgl, row_of_iso m, h₀] at h'
    have hp₀ : parentND₃ z₀ = e := Subtype.ext (parentSE₃_firstPiece₃ ψ.data π e.1)
    rw [hp₀] at h'
    exact (Option.some_injective _ h').symm

end Injective

end GenusSixExistence.Tripod.Gluing

end
