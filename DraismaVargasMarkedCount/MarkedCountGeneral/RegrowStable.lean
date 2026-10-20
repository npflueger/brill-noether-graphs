module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowSurvivors

@[expose] public section

/-!
# Regrowth, part 7: the stable graph of the regrown datum

With the dangling dictionary, the stable graph of `regrowDatum β` is the marked
stable graph of `ψ` (marks `markSet β.mark`) with the caterpillar at every mark:

* `stablePathEquiv : StablePath R ≃ MarkedStablePath ψ marks ⊕ TE c`: the marked rows of `ψ`, and
  one row per tail slot (a path or bridge row is its block edge; a loop row is the two loop edges,
  which meet at the tip, the only new vertex of surviving valency two);
* `branchVertexEquiv : MarkedBranchVertex ψ marks ⊕ (Σ j, CatVertex (c j)) ≃ BranchVertex R`: the
  marked vertices of `ψ` (a mark gains the first path edge and becomes trivalent), the spine blocks
  `B_i` and the bulbs `A_i`;
* the incidence counts by rows (`incidenceCount_tagPath`), trivalence and path ends.

Hypotheses: `ψ` connected, `T` a tree, every mark with a surviving edge (`hMark`), and for the
vertex statements the marks distinct (`hInj`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.Count.MarkedCount (MarkedStablePath MarkedBranchVertex MarkedConsecutive
  markedRow markedRow_eq_of_markedConsecutive markedIncidenceCount HasMarkedPathEnds
  IsMarkedPathEnd markSet mem_markSet)

namespace TailChain

variable {d c : ℕ} (ch : TailChain d c)

/-- The sheet naming the row over a slot: the block's name, or the bulb's name for a loop. -/
def rowAnchor : CatSlot c → Fin d
  | Sum.inl i => ch.eA (Sum.inl i)
  | Sum.inr (Sum.inl i) => ch.eA (Sum.inr (Sum.inl i))
  | Sum.inr (Sum.inr i) => ch.vA (bulb i)

variable {ch} in
theorem Valid.rowAnchor_mem (h : ch.Valid) (s : CatSlot c) : ch.rowAnchor s ∈ ch.rowIdx s := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact Finset.mem_singleton_self _
  · exact Finset.mem_singleton_self _
  · exact h.vA_mem (bulb i)

end TailChain

/-- The end of the row of a slot at a branch vertex: its head for a path or bridge slot, the bulb
for a leaf edge. -/
def rowEnd {c : ℕ} : CatSlot c → TailV c
  | Sum.inl i => lHead (Sum.inl i)
  | Sum.inr (Sum.inl i) => lHead (Sum.inr (Sum.inl i))
  | Sum.inr (Sum.inr i) => bulb i

namespace CatBranching

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c)

/-- The marks, as a finset of source vertices of `ψ`. -/
abbrev marks : Finset ψ.SourceVertex := markSet β.mark

theorem mem_marks_iff (Y : ψ.SourceVertex) : Y ∈ β.marks ↔ ∃ j, β.mark j = Y := by
  simp [marks, markSet]

theorem markCount_eq_zero_iff (Y : ψ.SourceVertex) : β.markCount Y = 0 ↔ Y ∉ β.marks := by
  unfold markCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff, mem_marks_iff]
  simp

theorem markCount_eq_ite (hInj : Function.Injective β.mark) (Y : ψ.SourceVertex) :
    β.markCount Y = if Y ∈ β.marks then 1 else 0 := by
  split_ifs with hY
  · obtain ⟨j, rfl⟩ := (β.mem_marks_iff _).mp hY
    unfold markCount
    rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    simp [hInj.eq_iff]
  · exact (β.markCount_eq_zero_iff Y).mpr hY

/-- The sheet naming the row over a tail slot. -/
def rowAnchor (t : TE c) : Fin d := (β.chain t.1).rowAnchor t.2

theorem rowAnchor_mem (t : TE c) : β.rowAnchor t ∈ β.rowIdx t := (β.valid t.1).rowAnchor_mem t.2

variable (hψ : ψ.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
  (hMark : ∀ j, nonDanglingValency ψ (β.mark j) ≠ 0)

/-! ## 1.  The surviving edges -/

/-- An old surviving edge, in the regrowth. -/
def oldND (F : NonDanglingEdge ψ) : NonDanglingEdge β.regrowDatum :=
  ⟨β.psiSE F.1, (β.not_isDangling_iff hψ hT hT0 hMark _).mpr (Or.inl ⟨F.1, F.2, rfl⟩)⟩

/-- A surviving tail edge. -/
def tailND (t : TE c) {q : Fin d} (hq : q ∈ β.rowSet t) : NonDanglingEdge β.regrowDatum :=
  ⟨β.tailSE t q, (β.not_isDangling_iff hψ hT hT0 hMark _).mpr (Or.inr ⟨t, q, hq, rfl⟩)⟩

/-- The surviving edge naming the row of a tail slot. -/
def rowND (t : TE c) : NonDanglingEdge β.regrowDatum :=
  β.tailND hψ hT hT0 hMark t (β.rowIdx_sub_rowSet t (β.rowAnchor_mem t))

theorem nonDanglingEdge_cases (E : NonDanglingEdge β.regrowDatum) :
    (∃ F, E = β.oldND hψ hT hT0 hMark F) ∨
      ∃ t q, ∃ hq : q ∈ β.rowSet t, E = β.tailND hψ hT hT0 hMark t hq := by
  rcases (β.not_isDangling_iff hψ hT hT0 hMark E.1).mp E.2 with ⟨F, hF, h⟩ | ⟨t, q, hq, h⟩
  · exact Or.inl ⟨⟨F, hF⟩, Subtype.ext h⟩
  · exact Or.inr ⟨t, q, hq, Subtype.ext h⟩

theorem oldND_injective : Function.Injective (β.oldND hψ hT hT0 hMark) := fun _ _ h ↦
  Subtype.ext (β.psiSE_injective (congrArg Subtype.val h))

/-! ## 2.  Surviving valency two -/

include hψ hT hT0 hMark

omit hT hT0 in
theorem two_le_nonDanglingValency_mark (j : Fin k) : 2 ≤ nonDanglingValency ψ (β.mark j) := by
  have h1 := hMark j
  have h2 := NonDanglingValency.nonDanglingValency_ne_one ψ hψ (β.mark j)
  omega

theorem three_le_nonDanglingValency_psiSV_mark (j : Fin k) :
    3 ≤ nonDanglingValency β.regrowDatum (β.psiSV (β.mark j)) := by
  rw [β.nonDanglingValency_psiSV hψ hT hT0 hMark]
  have h1 := β.two_le_nonDanglingValency_mark hψ hMark j
  have h2 : β.markCount (β.mark j) ≠ 0 := by
    rw [Ne, markCount_eq_zero_iff, not_not, mem_marks_iff]
    exact ⟨j, rfl⟩
  omega

theorem nonDanglingValency_psiSV_eq_two_iff (Y : ψ.SourceVertex) :
    nonDanglingValency β.regrowDatum (β.psiSV Y) = 2 ↔
      nonDanglingValency ψ Y = 2 ∧ Y ∉ β.marks := by
  constructor
  · intro h
    by_cases hY : Y ∈ β.marks
    · obtain ⟨j, rfl⟩ := (β.mem_marks_iff _).mp hY
      have := β.three_le_nonDanglingValency_psiSV_mark hψ hT hT0 hMark j
      omega
    · rw [β.nonDanglingValency_psiSV hψ hT hT0 hMark, (β.markCount_eq_zero_iff Y).mpr hY,
        add_zero] at h
      exact ⟨h, hY⟩
  · rintro ⟨h, hY⟩
    rw [β.nonDanglingValency_psiSV hψ hT hT0 hMark, (β.markCount_eq_zero_iff Y).mpr hY, h]

/-- **The new vertices of surviving valency two are the tips.** -/
theorem eq_tip_of_two {X : β.regrowDatum.SourceVertex}
    (hX : nonDanglingValency β.regrowDatum X = 2) (hOld : ∀ Y, X ≠ β.psiSV Y) :
    ∃ j i, X = β.blockSV ⟨j, tip i⟩ := by
  rcases β.sourceVertex_cases X with ⟨Y, rfl⟩ | ⟨v, n, rfl⟩ | ⟨⟨j, w⟩, q, rfl⟩
  · exact absurd rfl (hOld Y)
  · rw [β.nonDanglingValency_newSV hψ hT hT0 hMark] at hX; omega
  · rcases β.tailSV_cases ⟨j, w⟩ q with h | h
    · rw [h] at hX ⊢
      rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [β.nonDanglingValency_spine hψ hT hT0 hMark] at hX; omega
      · rw [β.nonDanglingValency_bulb hψ hT hT0 hMark] at hX; omega
      · exact ⟨j, i, rfl⟩
    · rw [β.nonDanglingValency_tailSV_of_not_mem hψ hT hT0 hMark h] at hX; omega

/-! ## 3.  The rows -/

omit hψ hT hT0 hMark in
theorem tailSE_eq_tailSE_iff_fst {t t' : TE c} {q q' : Fin d}
    (h : β.tailSE t q = β.tailSE t' q') : t = t' := ((β.tailSE_eq_iff _ _ _ _).mp h).1

open Classical in
/-- **The row of a surviving edge**: a marked row of `ψ`, or a tail slot. -/
def rowTag (E : NonDanglingEdge β.regrowDatum) : MarkedStablePath ψ β.marks ⊕ TE c :=
  if h : ∃ F : NonDanglingEdge ψ, E.1 = β.psiSE F.1 then .inl (markedRow β.marks h.choose)
  else if h' : ∃ t q, E.1 = β.tailSE t q then .inr h'.choose
  else False.elim (by
    rcases β.nonDanglingEdge_cases hψ hT hT0 hMark E with ⟨F, rfl⟩ | ⟨t, q, hq, rfl⟩
    · exact h ⟨F, rfl⟩
    · exact h' ⟨t, q, rfl⟩)

theorem rowTag_oldND (F : NonDanglingEdge ψ) :
    β.rowTag hψ hT hT0 hMark (β.oldND hψ hT hT0 hMark F) = .inl (markedRow β.marks F) := by
  have h : ∃ F' : NonDanglingEdge ψ, (β.oldND hψ hT hT0 hMark F).1 = β.psiSE F'.1 := ⟨F, rfl⟩
  unfold rowTag
  rw [dite_eq_left h]
  congr 2
  exact Subtype.ext (β.psiSE_injective h.choose_spec).symm

theorem rowTag_tailND (t : TE c) {q : Fin d} (hq : q ∈ β.rowSet t) :
    β.rowTag hψ hT hT0 hMark (β.tailND hψ hT hT0 hMark t hq) = .inr t := by
  have h0 : ¬ ∃ F' : NonDanglingEdge ψ, (β.tailND hψ hT hT0 hMark t hq).1 = β.psiSE F'.1 :=
    fun ⟨F', h⟩ ↦ β.psiSE_ne_tailSE F'.1 t q h.symm
  have h : ∃ t' q', (β.tailND hψ hT hT0 hMark t hq).1 = β.tailSE t' q' := ⟨t, q, rfl⟩
  unfold rowTag
  rw [dite_eq_right h0, dite_eq_left h]
  congr 1
  obtain ⟨q', hq'⟩ := h.choose_spec
  exact (β.tailSE_eq_tailSE_iff_fst hq').symm

/-- A surviving edge at a tip is a loop edge of its branch. -/
theorem eq_loop_of_incident_tip (E : NonDanglingEdge β.regrowDatum) (j : Fin k)
    (i : Fin (c j + 1)) (hE : Incident β.regrowDatum E.1 (β.blockSV ⟨j, tip i⟩)) :
    β.rowTag hψ hT hT0 hMark E = .inr ⟨j, loop i⟩ := by
  rcases β.nonDanglingEdge_cases hψ hT hT0 hMark E with ⟨F, rfl⟩ | ⟨t, q, hq, rfl⟩
  · exact absurd hE (β.incident_psiSE_tailSV _ _ _)
  · rw [rowTag_tailND]
    have h := (β.incident_tailSE_blockSV hq ⟨j, tip i⟩).mp hE
    obtain ⟨j', s⟩ := t
    obtain rfl := tail_incident_mark c β.x h
    have hs := (tail_incident_iff c β.x j' s (tip i)).mp h
    rw [incSlots_tip, Finset.mem_singleton] at hs
    rw [hs]

omit hψ hT hT0 hMark in
/-- A surviving tail edge never meets an old vertex that is not a mark. -/
theorem not_incident_tail_psiSV {t : TE c} {q : Fin d} (hq : q ∈ β.rowSet t)
    {Y : ψ.SourceVertex} (hY : Y ∉ β.marks) :
    ¬ Incident β.regrowDatum (β.tailSE t q) (β.psiSV Y) := by
  intro h
  rcases (β.incident_tailSE_of_rowSet hq _).mp h with h | h
  · obtain ⟨-, h'⟩ := (β.tailBlock_eq_psiSV_iff t Y).mp h.symm
    exact hY ((β.mem_marks_iff Y).mpr ⟨t.1, h'⟩)
  · exact β.psiSV_ne_tailSV _ _ _ h

/-- **Consecutive surviving edges have the same row.** -/
theorem rowTag_eq_of_consecutive {E E' : NonDanglingEdge β.regrowDatum}
    (h : Consecutive β.regrowDatum E E') :
    β.rowTag hψ hT hT0 hMark E = β.rowTag hψ hT hT0 hMark E' := by
  obtain ⟨hne, X, hE, hE', hX⟩ := h
  by_cases hOld : ∃ Y, X = β.psiSV Y
  · obtain ⟨Y, rfl⟩ := hOld
    obtain ⟨hTwo, hNot⟩ := (β.nonDanglingValency_psiSV_eq_two_iff hψ hT hT0 hMark Y).mp hX
    rcases β.nonDanglingEdge_cases hψ hT hT0 hMark E with ⟨F, rfl⟩ | ⟨t, q, hq, rfl⟩
    · rcases β.nonDanglingEdge_cases hψ hT hT0 hMark E' with ⟨F', rfl⟩ | ⟨t', q', hq', rfl⟩
      · rw [rowTag_oldND, rowTag_oldND]
        refine congrArg Sum.inl (markedRow_eq_of_markedConsecutive ⟨fun hFF ↦ hne ?_, Y,
          (β.incident_psiSE_psiSV _ _).mp hE, (β.incident_psiSE_psiSV _ _).mp hE', hTwo, hNot⟩)
        rw [hFF]
      · exact absurd hE' (β.not_incident_tail_psiSV hq' hNot)
    · exact absurd hE (β.not_incident_tail_psiSV hq hNot)
  · push Not at hOld
    obtain ⟨j, i, rfl⟩ := β.eq_tip_of_two hψ hT hT0 hMark hX fun Y h ↦ hOld Y h
    rw [β.eq_loop_of_incident_tip hψ hT hT0 hMark E j i hE,
      β.eq_loop_of_incident_tip hψ hT hT0 hMark E' j i hE']

/-- The row of a stable path of the regrowth. -/
def pathTag : StablePath β.regrowDatum → MarkedStablePath ψ β.marks ⊕ TE c :=
  Quot.lift (β.rowTag hψ hT hT0 hMark) fun _ _ h ↦ β.rowTag_eq_of_consecutive hψ hT hT0 hMark h

/-- Marked consecutiveness in `ψ` is consecutiveness in the regrowth. -/
theorem consecutive_oldND {F F' : NonDanglingEdge ψ}
    (h : MarkedConsecutive ψ β.marks F F') :
    Consecutive β.regrowDatum (β.oldND hψ hT hT0 hMark F) (β.oldND hψ hT hT0 hMark F') := by
  obtain ⟨hne, Y, hF, hF', hTwo, hNot⟩ := h
  refine ⟨fun h ↦ hne (Subtype.ext (β.psiSE_injective (congrArg Subtype.val h))), β.psiSV Y,
    (β.incident_psiSE_psiSV _ _).mpr hF, (β.incident_psiSE_psiSV _ _).mpr hF', ?_⟩
  exact (β.nonDanglingValency_psiSV_eq_two_iff hψ hT hT0 hMark Y).mpr ⟨hTwo, hNot⟩

/-- The stable path of the regrowth with a given row. -/
def tagPath : MarkedStablePath ψ β.marks ⊕ TE c → StablePath β.regrowDatum
  | .inl P => Quot.lift (fun F ↦ (β.oldND hψ hT hT0 hMark F).stablePath)
      (fun _ _ h ↦ stablePath_eq_of_consecutive (β.consecutive_oldND hψ hT hT0 hMark h)) P
  | .inr t => (β.rowND hψ hT hT0 hMark t).stablePath

theorem tagPath_inl_markedRow (F : NonDanglingEdge ψ) :
    β.tagPath hψ hT hT0 hMark (.inl (markedRow β.marks F)) =
      (β.oldND hψ hT hT0 hMark F).stablePath := rfl

theorem tagPath_inr (t : TE c) :
    β.tagPath hψ hT hT0 hMark (.inr t) = (β.rowND hψ hT hT0 hMark t).stablePath := rfl

/-- Every surviving tail edge lies on the row of its slot. -/
theorem stablePath_tailND (t : TE c) {q : Fin d} (hq : q ∈ β.rowSet t) :
    (β.tailND hψ hT hT0 hMark t hq).stablePath = (β.rowND hψ hT hT0 hMark t).stablePath := by
  obtain ⟨j, s⟩ := t
  by_cases hs : ∃ i, s = loop i
  · obtain ⟨i, rfl⟩ := hs
    by_cases hqa : q = β.rowAnchor ⟨j, loop i⟩
    · subst hqa; rfl
    · refine stablePath_eq_of_consecutive ⟨fun h ↦ hqa ?_, β.blockSV ⟨j, tip i⟩, ?_, ?_,
        β.nonDanglingValency_tip hψ hT hT0 hMark j i⟩
      · have h' := congrArg Subtype.val h
        exact β.tailSE_rowIdx_inj (show q ∈ β.rowIdx ⟨j, loop i⟩ from hq) (β.rowAnchor_mem _) h'
      · change Incident β.regrowDatum (β.tailSE ⟨j, loop i⟩ q) _
        rw [β.incident_tailSE_blockSV hq, tail_incident_iff, incSlots_tip]
        exact Finset.mem_singleton_self _
      · change Incident β.regrowDatum (β.tailSE ⟨j, loop i⟩ (β.rowAnchor ⟨j, loop i⟩)) _
        rw [β.incident_tailSE_blockSV (β.rowIdx_sub_rowSet _ (β.rowAnchor_mem _)),
          tail_incident_iff, incSlots_tip]
        exact Finset.mem_singleton_self _
  · push Not at hs
    have hq' : q ∈ β.eB ⟨j, s⟩ := by
      change q ∈ (β.chain j).rowSet s at hq
      rwa [TailChain.rowSet_of_not_loop _ hs] at hq
    have ha : β.rowAnchor ⟨j, s⟩ ∈ β.eB ⟨j, s⟩ := by
      have := β.rowIdx_sub_rowSet _ (β.rowAnchor_mem ⟨j, s⟩)
      change _ ∈ (β.chain j).rowSet s at this
      rwa [TailChain.rowSet_of_not_loop _ hs] at this
    have : β.tailND hψ hT hT0 hMark ⟨j, s⟩ hq = β.rowND hψ hT hT0 hMark ⟨j, s⟩ := by
      apply Subtype.ext
      change β.tailSE ⟨j, s⟩ q = β.tailSE ⟨j, s⟩ (β.rowAnchor ⟨j, s⟩)
      rw [β.tailSE_of_mem hq', β.tailSE_of_mem ha]
    rw [this]

/-- **The stable paths of the regrowth**: the marked rows of `ψ`, and one row per tail slot. -/
def stablePathEquiv : StablePath β.regrowDatum ≃ MarkedStablePath ψ β.marks ⊕ TE c where
  toFun := β.pathTag hψ hT hT0 hMark
  invFun := β.tagPath hψ hT hT0 hMark
  left_inv path := by
    induction path using Quot.ind with
    | mk E =>
      change β.tagPath hψ hT hT0 hMark (β.rowTag hψ hT hT0 hMark E) = E.stablePath
      rcases β.nonDanglingEdge_cases hψ hT hT0 hMark E with ⟨F, rfl⟩ | ⟨t, q, hq, rfl⟩
      · rw [rowTag_oldND]; rfl
      · rw [rowTag_tailND, tagPath_inr, stablePath_tailND]
  right_inv tag := by
    rcases tag with P | t
    · induction P using Quot.ind with
      | mk F => exact β.rowTag_oldND hψ hT hT0 hMark F
    · exact β.rowTag_tailND hψ hT hT0 hMark t _

theorem stablePathEquiv_symm_apply (tag : MarkedStablePath ψ β.marks ⊕ TE c) :
    (β.stablePathEquiv hψ hT hT0 hMark).symm tag = β.tagPath hψ hT hT0 hMark tag := rfl

theorem stablePathEquiv_stablePath (E : NonDanglingEdge β.regrowDatum) :
    β.stablePathEquiv hψ hT hT0 hMark E.stablePath = β.rowTag hψ hT hT0 hMark E := rfl

theorem stablePath_eq_tagPath_iff (E : NonDanglingEdge β.regrowDatum)
    (tag : MarkedStablePath ψ β.marks ⊕ TE c) :
    E.stablePath = β.tagPath hψ hT hT0 hMark tag ↔ β.rowTag hψ hT hT0 hMark E = tag := by
  rw [← stablePathEquiv_symm_apply, Equiv.eq_symm_apply]
  rfl

/-! ## 4.  Sums over the surviving edges -/

/-- The forward map of the decomposition of the surviving edges. -/
def ndOfSum : NonDanglingEdge ψ ⊕ (Σ t : TE c, {q // q ∈ β.rowIdx t}) →
    NonDanglingEdge β.regrowDatum
  | .inl F => β.oldND hψ hT hT0 hMark F
  | .inr ⟨t, q⟩ => β.tailND hψ hT hT0 hMark t (β.rowIdx_sub_rowSet t q.2)

theorem ndOfSum_bijective : Function.Bijective (β.ndOfSum hψ hT hT0 hMark) := by
  have hsurv : ∀ z, (β.ndOfSum hψ hT hT0 hMark z).1 = (β.survOfSum z).1 := by
    rintro (F | ⟨t, q⟩) <;> rfl
  constructor
  · intro z z' h
    apply β.survOfSum_bijective.1
    apply Subtype.ext
    rw [← hsurv, ← hsurv, h]
  · intro E
    obtain ⟨z, hz⟩ := β.survOfSum_bijective.2
      ⟨E.1, (β.not_isDangling_iff hψ hT hT0 hMark E.1).mp E.2⟩
    exact ⟨z, Subtype.ext (by rw [hsurv, hz])⟩

/-- **Sums over the surviving edges of the regrowth.** -/
theorem sum_nonDanglingEdge {M : Type*} [AddCommMonoid M]
    (f : NonDanglingEdge β.regrowDatum → M) :
    ∑ E, f E = ∑ F, f (β.oldND hψ hT hT0 hMark F) +
      ∑ t, ∑ q : {q // q ∈ β.rowIdx t}, f (β.tailND hψ hT hT0 hMark t (β.rowIdx_sub_rowSet t q.2)) := by
  rw [← Fintype.sum_bijective _ (β.ndOfSum_bijective hψ hT hT0 hMark)
    (fun z ↦ f (β.ndOfSum hψ hT hT0 hMark z)) f (fun _ ↦ rfl), Fintype.sum_sum_type,
    Fintype.sum_sigma]
  rfl

/-! ## 5.  Incidence counts -/

omit hψ hT hT0 hMark in
open Classical in
theorem incidenceCount_eq_sum (X : β.regrowDatum.SourceVertex)
    (path : StablePath β.regrowDatum) :
    StablePathCount.incidenceCount β.regrowDatum X path =
      ∑ E : NonDanglingEdge β.regrowDatum,
        if Incident β.regrowDatum E.1 X ∧ E.stablePath = path then 1 else 0 := by
  unfold StablePathCount.incidenceCount StablePathCount.incidentEdges
  rw [Finset.filter_filter, Finset.card_filter]

omit hψ hT hT0 hMark in
open Classical in
theorem markedIncidenceCount_eq_sum (Y : ψ.SourceVertex) (P : MarkedStablePath ψ β.marks) :
    markedIncidenceCount ψ β.marks Y P =
      ∑ F : NonDanglingEdge ψ, if Incident ψ F.1 Y ∧ markedRow β.marks F = P then 1 else 0 := by
  unfold markedIncidenceCount StablePathCount.incidentEdges
  rw [Finset.filter_filter, Finset.card_filter]

open Classical in
/-- An incidence count of the regrowth, by rows. -/
theorem incidenceCount_tagPath (X : β.regrowDatum.SourceVertex)
    (tag : MarkedStablePath ψ β.marks ⊕ TE c) :
    StablePathCount.incidenceCount β.regrowDatum X (β.tagPath hψ hT hT0 hMark tag) =
      (∑ F : NonDanglingEdge ψ,
          if Incident β.regrowDatum (β.psiSE F.1) X ∧ Sum.inl (markedRow β.marks F) = tag
            then 1 else 0) +
        ∑ t, ∑ q : {q // q ∈ β.rowIdx t},
          if Incident β.regrowDatum (β.tailSE t q.1) X ∧ Sum.inr t = tag then 1 else 0 := by
  rw [incidenceCount_eq_sum, sum_nonDanglingEdge β hψ hT hT0 hMark]
  simp only [stablePath_eq_tagPath_iff, rowTag_oldND, rowTag_tailND]
  rfl

theorem incidenceCount_psiSV_inl (Y : ψ.SourceVertex) (P : MarkedStablePath ψ β.marks) :
    StablePathCount.incidenceCount β.regrowDatum (β.psiSV Y) (β.tagPath hψ hT hT0 hMark (.inl P)) =
      markedIncidenceCount ψ β.marks Y P := by
  classical
  rw [incidenceCount_tagPath, markedIncidenceCount_eq_sum]
  simp only [incident_psiSE_psiSV, Sum.inl.injEq, reduceCtorEq, and_false, ite_false,
    Finset.sum_const_zero, add_zero]

theorem incidenceCount_psiSV_inr (Y : ψ.SourceVertex) (t : TE c) :
    StablePathCount.incidenceCount β.regrowDatum (β.psiSV Y) (β.tagPath hψ hT hT0 hMark (.inr t)) =
      if t.2 = path 0 ∧ β.mark t.1 = Y then 1 else 0 := by
  classical
  rw [incidenceCount_tagPath]
  simp only [reduceCtorEq, and_false, ite_false, Finset.sum_const_zero, zero_add, Sum.inr.injEq]
  rw [Finset.sum_eq_single t]
  · have h : ∀ q : {q // q ∈ β.rowIdx t},
        Incident β.regrowDatum (β.tailSE t q.1) (β.psiSV Y) ↔ (t.2 = path 0 ∧ β.mark t.1 = Y) := by
      intro q
      rw [β.incident_tailSE_of_rowSet (β.rowIdx_sub_rowSet t q.2), eq_comm,
        β.tailBlock_eq_psiSV_iff]
      simp [blockSV]
    simp only [and_true, h, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    by_cases ht : t.2 = path 0 ∧ β.mark t.1 = Y
    · simp only [ht, and_self, ite_true, mul_one]
      rw [card_rowIdx, ite_eq_right (by rw [ht.1]; simp)]
    · simp only [ht, ite_false, mul_zero]
  · intro t' _ ht'
    exact Finset.sum_eq_zero fun q _ ↦ ite_eq_right fun h ↦ ht' h.2
  · simp

theorem incidenceCount_tailSV_inl (w : TV c) (q : Fin d) (P : MarkedStablePath ψ β.marks) :
    StablePathCount.incidenceCount β.regrowDatum (β.tailSV w q)
      (β.tagPath hψ hT hT0 hMark (.inl P)) = 0 := by
  classical
  rw [incidenceCount_tagPath]
  simp

theorem incidenceCount_blockSV_inr (w : TV c) (t : TE c) :
    StablePathCount.incidenceCount β.regrowDatum (β.blockSV w)
      (β.tagPath hψ hT hT0 hMark (.inr t)) =
      if tailEnd c β.x t = tailV c β.x w ∨ headEnd c β.x t = tailV c β.x w then
        (β.rowIdx t).card else 0 := by
  classical
  rw [incidenceCount_tagPath]
  simp only [incident_psiSE_tailSV, blockSV, false_and, ite_false, Finset.sum_const_zero,
    zero_add, Sum.inr.injEq]
  rw [Finset.sum_eq_single t]
  · have h : ∀ q : {q // q ∈ β.rowIdx t},
        Incident β.regrowDatum (β.tailSE t q.1) (β.tailSV w (β.vA w)) ↔
          (tailEnd c β.x t = tailV c β.x w ∨ headEnd c β.x t = tailV c β.x w) :=
      fun q ↦ β.incident_tailSE_blockSV (β.rowIdx_sub_rowSet t q.2) w
    simp only [and_true, h, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    split_ifs <;> simp
  · intro t' _ ht'
    exact Finset.sum_eq_zero fun q _ ↦ ite_eq_right fun h ↦ ht' h.2
  · simp

/-! ## 6.  The branch vertices -/

variable (hInj : Function.Injective β.mark)

include hInj

theorem three_le_nonDanglingValency_psiSV_iff (Y : ψ.SourceVertex) :
    3 ≤ nonDanglingValency β.regrowDatum (β.psiSV Y) ↔
      3 ≤ nonDanglingValency ψ Y ∨ Y ∈ β.marks := by
  rw [β.nonDanglingValency_psiSV hψ hT hT0 hMark, β.markCount_eq_ite hInj]
  split_ifs with hY
  · obtain ⟨j, rfl⟩ := (β.mem_marks_iff _).mp hY
    have := β.two_le_nonDanglingValency_mark hψ hMark j
    simp only [hY, or_true, iff_true]
    omega
  · simp [hY]

omit hInj in
theorem nonDanglingValency_blockSV_catVertex (j : Fin k) (w : CatVertex (c j)) :
    nonDanglingValency β.regrowDatum (β.blockSV ⟨j, Sum.inl w⟩) = 3 := by
  rcases w with i | i
  · exact β.nonDanglingValency_spine hψ hT hT0 hMark j i
  · exact β.nonDanglingValency_bulb hψ hT hT0 hMark j i

/-- The map onto the branch vertices of the regrowth. -/
def bvOfSum : MarkedBranchVertex ψ β.marks ⊕ (Σ j, CatVertex (c j)) →
    BranchVertex β.regrowDatum
  | .inl Y => ⟨β.psiSV Y.1,
      (β.three_le_nonDanglingValency_psiSV_iff hψ hT hT0 hMark hInj Y.1).mpr Y.2⟩
  | .inr ⟨j, w⟩ => ⟨β.blockSV ⟨j, Sum.inl w⟩,
      (β.nonDanglingValency_blockSV_catVertex hψ hT hT0 hMark j w).ge⟩

theorem bvOfSum_bijective : Function.Bijective (β.bvOfSum hψ hT hT0 hMark hInj) := by
  constructor
  · rintro (Y | ⟨j, w⟩) (Y' | ⟨j', w'⟩) h <;> have h' := congrArg Subtype.val h <;>
      simp only [bvOfSum, psiSV_inj, blockSV_inj] at h'
    · exact congrArg Sum.inl (Subtype.ext h')
    · exact absurd h' (β.psiSV_ne_tailSV _ _ _)
    · exact absurd h' (β.tailSV_ne_psiSV _ _ _)
    · obtain ⟨rfl, h''⟩ := Sigma.mk.inj_iff.mp h'
      have := Sum.inl_injective (eq_of_heq h'')
      subst this
      rfl
  · rintro ⟨X, hX⟩
    rcases β.sourceVertex_cases X with ⟨Y, rfl⟩ | ⟨v, n, rfl⟩ | ⟨⟨j, w⟩, q, rfl⟩
    · exact ⟨.inl ⟨Y, (β.three_le_nonDanglingValency_psiSV_iff hψ hT hT0 hMark hInj Y).mp hX⟩,
        rfl⟩
    · rw [β.nonDanglingValency_newSV hψ hT hT0 hMark] at hX; omega
    · rcases β.tailSV_cases ⟨j, w⟩ q with h | h
      · rcases w with w | i
        · exact ⟨.inr ⟨j, w⟩, Subtype.ext h.symm⟩
        · rw [h] at hX
          change 3 ≤ nonDanglingValency β.regrowDatum (β.blockSV ⟨j, tip i⟩) at hX
          rw [β.nonDanglingValency_tip hψ hT hT0 hMark] at hX; omega
      · rw [β.nonDanglingValency_tailSV_of_not_mem hψ hT hT0 hMark h] at hX; omega

/-- **The branch vertices of the regrowth**: the marked vertices of `ψ`, the spine blocks and the
bulbs. -/
def branchVertexEquiv :
    MarkedBranchVertex ψ β.marks ⊕ (Σ j, CatVertex (c j)) ≃ BranchVertex β.regrowDatum :=
  Equiv.ofBijective _ (β.bvOfSum_bijective hψ hT hT0 hMark hInj)

theorem branchVertexEquiv_inl (Y : MarkedBranchVertex ψ β.marks) :
    (β.branchVertexEquiv hψ hT hT0 hMark hInj (.inl Y)).1 = β.psiSV Y.1 := rfl

theorem branchVertexEquiv_inr (j : Fin k) (w : CatVertex (c j)) :
    (β.branchVertexEquiv hψ hT hT0 hMark hInj (.inr ⟨j, w⟩)).1 = β.blockSV ⟨j, Sum.inl w⟩ := rfl

omit hInj

/-! ## 7.  Trivalence and path ends -/

theorem nonDanglingValency_le_three (hTri : ∀ Y, nonDanglingValency ψ Y ≤ 3)
    (hTwo : ∀ j, nonDanglingValency ψ (β.mark j) = 2) (hInj : Function.Injective β.mark)
    (X : β.regrowDatum.SourceVertex) : nonDanglingValency β.regrowDatum X ≤ 3 := by
  rcases β.sourceVertex_cases X with ⟨Y, rfl⟩ | ⟨v, n, rfl⟩ | ⟨⟨j, w⟩, q, rfl⟩
  · rw [β.nonDanglingValency_psiSV hψ hT hT0 hMark, β.markCount_eq_ite hInj]
    split_ifs with hY
    · obtain ⟨j, rfl⟩ := (β.mem_marks_iff _).mp hY
      rw [hTwo j]
    · simpa using hTri Y
  · rw [β.nonDanglingValency_newSV hψ hT hT0 hMark]; omega
  · rcases β.tailSV_cases ⟨j, w⟩ q with h | h
    · rw [h]
      rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [β.nonDanglingValency_spine hψ hT hT0 hMark]
      · rw [β.nonDanglingValency_bulb hψ hT hT0 hMark]
      · rw [β.nonDanglingValency_tip hψ hT hT0 hMark]; omega
    · rw [β.nonDanglingValency_tailSV_of_not_mem hψ hT hT0 hMark h]; omega

theorem hasPathEnds_regrowDatum (hEnds : HasMarkedPathEnds ψ β.marks) :
    HasPathEnds β.regrowDatum := by
  intro E
  rcases β.nonDanglingEdge_cases hψ hT hT0 hMark E with ⟨F, rfl⟩ | ⟨t, q, hq, rfl⟩
  · obtain ⟨F', Y, hRow, hInc, hEnd⟩ := hEnds F
    refine ⟨β.oldND hψ hT hT0 hMark F', β.psiSV Y, ?_, (β.incident_psiSE_psiSV _ _).mpr hInc, ?_⟩
    · rw [← tagPath_inl_markedRow, ← tagPath_inl_markedRow, hRow]
    · intro hTwo
      obtain ⟨hTwo', hNot⟩ := (β.nonDanglingValency_psiSV_eq_two_iff hψ hT hT0 hMark Y).mp hTwo
      rcases hEnd with h | h
      · exact h hTwo'
      · exact hNot h
  · obtain ⟨j, s⟩ := t
    have hmem := β.rowIdx_sub_rowSet _ (β.rowAnchor_mem ⟨j, s⟩)
    refine ⟨β.rowND hψ hT hT0 hMark ⟨j, s⟩, β.blockSV ⟨j, rowEnd s⟩,
      (β.stablePath_tailND hψ hT hT0 hMark ⟨j, s⟩ hq).symm, ?_, ?_⟩
    · change Incident β.regrowDatum (β.tailSE ⟨j, s⟩ _) _
      rw [β.incident_tailSE_blockSV hmem, tail_incident_iff, mem_incSlots]
      rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (lTail_loop i)
    · rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · induction i using Fin.lastCases with
        | last =>
          rw [show rowEnd (path (Fin.last (c j))) = bulb (Fin.last (c j)) from lHead_path_last,
            β.nonDanglingValency_bulb hψ hT hT0 hMark]; omega
        | cast i =>
          rw [show rowEnd (path i.castSucc) = spine i from lHead_path_castSucc i,
            β.nonDanglingValency_spine hψ hT hT0 hMark]; omega
      · rw [show rowEnd (bridge i) = bulb i.castSucc from lHead_bridge i,
          β.nonDanglingValency_bulb hψ hT hT0 hMark]; omega
      · rw [show rowEnd (loop i) = bulb i from rfl, β.nonDanglingValency_bulb hψ hT hT0 hMark]
        omega

end CatBranching

end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
