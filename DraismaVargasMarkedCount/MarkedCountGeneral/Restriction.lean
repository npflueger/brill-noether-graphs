module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailIso
public import DraismaVargasMarkedCount.MarkedCount.Correspondence

@[expose] public section

/-!
# The two-point ramified count, module 7: restriction

A frame `φ` over the tailed core `T.H` (a caterpillar of genus `aⱼ = c j + 1` at every mark)
**restricts** to

* a lower index `J`: `J j` is the number of ascents of the slope sequence at mark `j`, the number
  of index-one copies of `T'` shed there (the preimage of `T'` is a connected component
  containing the core, plus one index-one copy of `T'` per ascent);
* a typed frame of type `lowerType c J = (aⱼ - 2 Jⱼ)ⱼ` (possibly `0`, an unramified mark kept in
  the core) in degree `d - Σⱼ Jⱼ` over the marked core (the restriction of `φ` to that
  component);
* the slope sequences, one per mark, with `J j` ascents (rigidity (3), module `Rigidity`).

This is `LowerFrame`; its class version is `LowerClass`. The map is request-free; its properties:

* `restrictTailed_respects`: it descends to classes;
* `coordsAt_restrictTailed`: the core columns of `φ` carry the coordinates of the restriction, and
  every other column a positive multiple of one tail length (`z_{t_i} = s_i ℓ(h_i)`, `2β`, `λ/2`),
  whatever the tail lengths;
* `typedAbsMult_restrictTailed`: **the tail factor is `1`**, `Mult_H(φ) = Mult(ψ; marks)`
  (`D_φ = D_ψ ∏ sᵢ 2^a`, `det A_φ = det A_ψ ∏ (1/sᵢ)`,
  `l(T) = l*(T') + a`), in absolute value (only `|Mult|` is formalized, as in the
  ramification-one count).

The construction is in the modules
`RestrictTail*` (namespace `TailRestrict`): the shape of the tails (`RestrictTailShape`), the
counts (`RestrictTailCount`), the lone sheets (`RestrictTailLone`, `RestrictTailShed`), the datum
(`RestrictTailDatum`), its marked rows and vertices (`RestrictTailRows`), the block decomposition of
the matrix (`RestrictTailFrame`), the marks and leaves (`RestrictTailMarks`), the typed frame and
its multiplicity (`RestrictTailTyped`) and the isomorphism invariance (`RestrictTailIso`). The
unfolding lemmas `restrictTailed_lowerIdx` ... `restrictTailed_ident_row` below are `rfl`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}

/-! ## 1.  Lower types -/

/-- **A lower index**: the number `J j ≤ aⱼ / 2` of shed sheets at mark `j`, `aⱼ = c j + 1`. -/
abbrev LowerIndex (c : Fin k → ℕ) : Type := ∀ j, Fin ((c j + 1) / 2 + 1)

/-- The lower type `aⱼ - 2 Jⱼ` (with `j` ascents, `s_1 = a + 1 - 2j`, and the type is
`a' = s_1 - 1`). -/
def lowerType (c : Fin k → ℕ) (J : LowerIndex c) : Fin k → ℕ := fun j ↦ c j + 1 - 2 * (J j : ℕ)

/-- The total number of shed sheets, the drop in degree. -/
def shed {c : Fin k → ℕ} (J : LowerIndex c) : ℕ := ∑ j, (J j : ℕ)

/-- The slope sequences at every mark, with `J j` ascents at mark `j`. -/
abbrev SlopeData (c : Fin k → ℕ) (J : LowerIndex c) : Type := ∀ j, SlopeSeq (c j + 1) (J j)

/-- **The headline degree** `2d = g + Σⱼ aⱼ + 2` of the tailed core, with
`g = p + 1 - n` the genus of the marked core. -/
def IsTailDegree (n p : ℕ) (c : Fin k → ℕ) (degree : ℕ) : Prop :=
  2 * degree = (p + 1 - n) + ∑ j, (c j + 1) + 2

/-- **The restriction data**: a lower index, a typed frame of the lower type in the lower degree,
and the slopes (the right side of the decomposition `Correspondence.openMultCount_tailed`, frame
by frame). -/
def LowerFrame (core : Core n p) (mark : Fin k → Fin n) (c : Fin k → ℕ) (degree : ℕ) : Type 1 :=
  Σ J : LowerIndex c, TypedFrame core mark (lowerType c J) (degree - shed J) × SlopeData c J

/-- **The right side of the decomposition**, on classes. -/
def LowerClass (core : Core n p) (mark : Fin k → Fin n) (c : Fin k → ℕ) (degree : ℕ) : Type 1 :=
  Σ J : LowerIndex c, TypedFrameClass core mark (lowerType c J) (degree - shed J) × SlopeData c J

/-- The class of restriction data. -/
def LowerFrame.toClass (z : LowerFrame core mark c degree) : LowerClass core mark c degree :=
  ⟨z.1, TypedFrameClass.mk z.2.1, z.2.2⟩

/-- Openness of a lower class: openness of its typed class. -/
def LowerClass.OpenAt (z : LowerClass core mark c degree) (y : Fin p → ℚ) : Prop :=
  z.2.1.OpenAt y

/-- The multiplicity of a lower class: that of its typed class (the tail factor is `1`). -/
noncomputable def LowerClass.mult (z : LowerClass core mark c degree) : ℚ := z.2.1.typedAbsMult

/-! ## 2.  Restriction -/

/-- **Restriction**.

*Construction.* By rigidity (module `Rigidity`, at every tail `T.caterpillarAt j`) the tail at mark
`j` is private: the target contains the subtree `T_tail,j` (`3aⱼ - 1` edges, attached at
`x_j = φ(u_j)` only), over which the only surviving elements are the tail's own, and the slopes
`s^{(j)}` form a slope sequence with `J j` ascents (`exists_slopeSeq`). Then:

1. delete the target vertices of every `T_tail,j` other than `x_j`, all at once, by an induced
   subgraph (the ramification-one `Restrict.restrictDatum`, with its dictionaries; partitions
   unchanged);
2. **split the components**: the restriction has
   `Σⱼ Jⱼ` components besides the core component, each an index-one copy of `T'` (one per ascent:
   the dangling edge of `B_i` over `t_i`); they are sheets that are singleton blocks everywhere
   over `T'`. Remove those sheets and renumber the remaining ones by `Fin (d - shed J)` (a generic
   sheet-deletion operation on gluing data; the joins are unchanged since the removed sheets are
   singletons). `GluingDatum.Valid` includes connectedness, so the datum is valid only after
   the split;
3. the marks are the core vertices `u_j` (`oldVertex (mark j)`), of surviving valency two; the
   marked rows are the stable paths of `φ` minus the tail rows, cut at the marks, i.e. the core
   slots (as the ramification-one `Lollipops.rowEquiv`); the labelling takes the kept target edges
   in any order;
4. (D4′) at `u_j` with type `aⱼ - 2Jⱼ`: `r_ψ(u_j) = r_φ(u_j) + s_1 - 1 ≥ s_1 - 1` and
   `m_ψ(u_j) = m_φ(u_j) ≥ s_1` (harmonicity over `t_1`), `s_1 = aⱼ + 1 - 2Jⱼ`;
5. `saturated`: `|E(T')| = |E(T)| - Σ (3aⱼ - 1)`, `g` drops by `Σ aⱼ`, `d` by `shed J`, and the
   excess is `Σ (aⱼ - 2Jⱼ - 1)`;
6. `det_ne_zero` from the block decomposition (`Rigidity.tail_block`). -/
noncomputable def restrictTailed (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) : LowerFrame core mark c degree :=
  ⟨TailRestrict.lowerIdx T hc f, TailRestrict.typedFrame T hc f, TailRestrict.slopeSeq T hc f⟩

/-! ### Unfolding lemmas

All `rfl`. The names on the right are those of modules `RestrictTail*` (namespace
`TailRestrict`); `sPath T hc M j i` is the index of the lone path edge `h_{i+1}` of tail `j`, i.e.
`|P_{i+1}|`. The degree of the restriction is `degree - shed J` **definitionally**. -/

theorem restrictTailed_lowerIdx (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) (j : Fin k) :
    ((restrictTailed T hc f).1 j : ℕ) = (c j + 2 - TailRestrict.sPath T hc (f.member 0) j 0) / 2 :=
  rfl

theorem restrictTailed_slope (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) (j : Fin k) (i : Fin (c j + 1)) :
    ((restrictTailed T hc f).2.2 j).1 i = TailRestrict.sPath T hc (f.member 0) j i := rfl

theorem shed_restrictTailed (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) :
    shed (restrictTailed T hc f).1 = TailRestrict.nShed T hc (f.member 0) :=
  TailRestrict.sum_lowerNat T hc f

theorem restrictTailed_target (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) :
    (restrictTailed T hc f).2.1.target = TailRestrict.rTarget T hc (f.member 0) := rfl

/-- The datum: `TailRestrict.dat` is the abbreviation
`Sheets.restrictSheets (rData T hc M) (split T hc M m hm) _ _`, the target restriction `rData`
with its lone sheets (`split`, by `Sheets.splitBy` on `loneSet`) deleted. -/
theorem restrictTailed_data (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) :
    (restrictTailed T hc f).2.1.data =
      TailRestrict.dat T hc (f.member 0) (degree - shed (restrictTailed T hc f).1)
        (TailRestrict.mDegAt_add T hc f _ fun _ ↦ rfl) := rfl

theorem restrictTailed_markSource (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) (j : Fin k) :
    (restrictTailed T hc f).2.1.markSource j =
      TailRestrict.markSrc T hc (f.member 0) (degree - shed (restrictTailed T hc f).1)
        (TailRestrict.mDegAt_add T hc f _ fun _ ↦ rfl) j := rfl

theorem restrictTailed_ident_vertex (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) :
    (restrictTailed T hc f).2.1.ident.vertex =
      TailRestrict.vertexEquiv T hc (f.member 0) (degree - shed (restrictTailed T hc f).1)
        (TailRestrict.mDegAt_add T hc f _ fun _ ↦ rfl) := rfl

theorem restrictTailed_ident_row (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) :
    (restrictTailed T hc f).2.1.ident.row =
      TailRestrict.rowEquiv T hc (f.member 0) (degree - shed (restrictTailed T hc f).1)
        (TailRestrict.mDegAt_add T hc f _ fun _ ↦ rfl) := rfl

/-- **Restriction descends to classes.** *Proof sketch.* An isomorphism over the identity
of `H` preserves the tail rows, hence the slopes (the indices of the lone path edges) and the
shed sheets; it restricts (`Restrict.restrictIso`) to an isomorphism of the restricted data, and
then of the sheet-deleted data, carrying marks to marks, over the identity of the marked core.
As the ramification-one `restrictFrame_respects`. -/
theorem restrictTailed_respects (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    {f f' : Frame T.H degree} (iso : FrameIso f f') :
    (restrictTailed T hc f).toClass = (restrictTailed T hc f').toClass := by
  have hJ' : ∀ j, ((TailRestrict.lowerIdx T hc f j : ℕ)) = TailRestrict.lowerNat T hc f' j :=
    fun j ↦ (TailRestrict.lowerNat_map T hc iso j).symm
  have key : ∀ (J : LowerIndex c) (h : ∀ j, (J j : ℕ) = TailRestrict.lowerNat T hc f' j),
      J = TailRestrict.lowerIdx T hc f' →
      (restrictTailed T hc f').toClass =
        ⟨J, TypedFrameClass.mk (TailRestrict.typedFrameAt T hc f' J h),
          TailRestrict.slopeSeqAt T hc f' J h⟩ := by
    rintro J h rfl
    rfl
  rw [key _ hJ' (TailRestrict.lowerIdx_map T hc iso).symm]
  change (⟨TailRestrict.lowerIdx T hc f,
      TypedFrameClass.mk (TailRestrict.typedFrameAt T hc f _ (fun _ ↦ rfl)),
      TailRestrict.slopeSeqAt T hc f _ (fun _ ↦ rfl)⟩ : LowerClass core mark c degree) = _
  rw [TailRestrict.slopeSeqAt_map T hc iso _ (fun _ ↦ rfl) hJ']
  exact congrArg (fun x ↦ (⟨TailRestrict.lowerIdx T hc f, x,
      TailRestrict.slopeSeqAt T hc f _ (fun _ ↦ rfl)⟩ : LowerClass core mark c degree))
    (TypedFrameClass.mk_eq_mk_of_iso ⟨TailRestrict.typedIso T hc iso _ (fun _ ↦ rfl) hJ'⟩)

/-- **The coordinates**: the core columns of `φ` at a
request `y_H` whose core part is `y` are the coordinates of the restriction at `y`, and every
other column is `weight · y_H(tail slot)` with a positive weight (`s_i`, `2`, `1/2`), whatever the
tail lengths. No positivity is assumed: this is linear algebra on the block decomposition. -/
theorem coordsAt_restrictTailed (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) :
    ∃ (col : Fin p → Fin T.P) (slotOf : Fin T.P → Fin T.P) (weight : Fin T.P → ℚ),
      (∀ e, (∀ i, col i ≠ e) → 0 < weight e ∧ ∃ j s, slotOf e = T.tailSlot j s) ∧
      ∀ (y : Fin p → ℚ) (yH : Fin T.P → ℚ), (∀ i, yH (T.coreSlot i) = y i) →
        (∀ i, f.coordsAt yH (col i) = (restrictTailed T hc f).2.1.coordsAt y i) ∧
        ∀ e, (∀ i, col i ≠ e) → f.coordsAt yH e = weight e * yH (slotOf e) := by
  refine ⟨TailRestrict.colIncl T hc (f.member 0), TailRestrict.slotOfCol T hc f,
    TailRestrict.weightOfCol T hc f, fun e he ↦ ?_, fun y yH hy ↦
      TailRestrict.coordsAt_typedFrame T hc f y yH hy⟩
  obtain ⟨q, hq⟩ := TailRestrict.exists_inr_of_not_col T hc f e he
  refine ⟨?_, q.1, q.2, ?_⟩
  · unfold TailRestrict.weightOfCol
    rw [hq]
    have := TailRestrict.tailWeight_pos T hc f q
    simp only [Sum.elim_inr]
    positivity
  · unfold TailRestrict.slotOfCol
    rw [hq]
    rfl

/-- **The tail factor is `1`**: `|Mult_H(φ)| = |Mult(ψ; marks)|`,
with the typed multiplicity `D det A / 2^{l*}` on the right. *Proof sketch.* `D_φ = D_ψ ∏ sᵢ 2^a`
(the row `h_i` has the single entry `1/sᵢ`, the bridges `1/2`, the loops `2`),
`|det A_φ| = |det A_ψ| ∏ (1/sᵢ)` (block diagonal), and
`l(T) = l(T') + a - [x leaf of T'] = l*(T') + a`: the leaves `v_i` are new, and `x` is a leaf of
`T'` iff it is divalent in `T` iff `φ` folds at `u`, which forces `aⱼ - 2Jⱼ ≥ 1` (a fold has
`m(u) = s_1 = p + q ≥ 2`), so `x` is then excluded from `l*`. -/
theorem typedAbsMult_restrictTailed (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (f : Frame T.H degree) : (restrictTailed T hc f).2.1.typedAbsMult = f.absMult :=
  TailRestrict.typedAbsMult_typedFrame T hc f

end DraismaVargas.Count.MarkedCountGeneral
