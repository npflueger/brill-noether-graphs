module

public import DraismaVargas.LocalCases.InteriorGraphTracking

@[expose] public section

/-!
# An incidence dictionary onto an arbitrary cubic dart graph, and onto a move

Source: Draisma--Vargas Part I (arXiv:1909.12924), the construction of the
stable graph `H(M)` of a gluing datum in Section 3 and the edge labellings a
limit inherits in Section 5; together with Vargas, Part II (arXiv:2609.09109),
Section 5.1 ("Combinatorial setup and local determinants"), where a
combinatorial type change is recorded as a Whitehead move on the *ambient
tracked graph*, not on a second cover.

`StableSourceDarts.isoOfIncidenceEquivalence` produces
`Iso (ofDatum data …) (ofDatum other …)` from a
`StableGraphIncidence.Equivalence`: a branch-vertex bijection, a stable-row
bijection, and equality of the row-filtered stars; the occurrence-level
bijections inside each star are then *chosen* by `Fintype.equivOfCardEq`.  Its
target is always a second cover's own stable graph.  The `tracks` field of
`OuterWalk.TypeChangeLink` needs the same construction with the target replaced
by `graph.move m`, where `graph` is the tracked ambient graph: there is no
second gluing datum in sight, and `graph.move m` is not `ofDatum` of anything.

## What is proved

* `DatumGraphIncidence data H`: the abstract notion of an incidence dictionary
  between the stable graph of a cover `data` and an arbitrary cubic dart graph
  `H`.  Its three fields are a branch-vertex bijection `vertex`, a *row label*
  `rowLabel : D → StablePath data` that is constant on `H`-edges
  (`rowLabel_op`), and the star equality `incidence`.  Carrying a row label
  constant on `op`-orbits is the same data as a bijection from stable rows onto
  the `op`-orbits of `H`, but needs no quotient.
* `isoOfDatumGraphIncidence`: the constructor
  `Iso (ofDatum data …) H` from such a dictionary.  The `op_map` field is proved
  from `StableSourceDarts.opposite_eq_of_row_eq` -- in the constructed graph the
  opposite dart is *characterised* as the other dart of the same row, so the
  dictionary's `rowLabel_op` plus `H.op_ne` pins it down.  No counting of darts
  per row on the `H` side is needed.
* `isoOfMovedIncidenceEquivalence`: the specialisation whose target is
  `G.move m₀`, stated directly against the permuted vertex map
  `fun d ↦ G.vert (m₀.perm d)` and the unchanged involution `G.op`.
* `tracksOfMovedIncidence`: the packaged `InteriorGraphTracking.Tracks fd
  (G.move m₀) label` obtained by taking `rowLabel := fd.labelling.row.symm ∘
  label`; the `row_map` half of `Tracks` then holds by construction.
* `label_op_of_tracks`: the `hOp` hypothesis is free from the *incoming*
  tracking datum -- the label of a dart is the chart coordinate of its stable
  row, and the two darts of an edge carry the same row -- so at a type change
  only the branch-vertex bijection and the star count are geometric input.
* `DatumGraphIncidence.self`, `card_fibre_ofDatum`: the non-vacuity witness --
  every cover's own stable graph carries its identity dictionary -- and the
  star count it rests on.
* `DatumGraphIncidence.ofIso`: any isomorphism onto `H` gives a dictionary, so
  the notion is exactly as strong as an isomorphism.

## Hypotheses left explicit here

Nothing here produces a `DatumGraphIncidence` at a wall: the branch-vertex
bijection and the star equality across a type change are the geometric input.
The bijection (`vertexEquiv`) is supplied, over `WallSplitIncidence` (the
incidence dictionary across a facet wall contraction) and the anchor stars of the
valency-two/three/four candidates, by `NonTrivalentValencyThreeTracks`
(Type III), `NonTrivalentValencyThreeSimpleTracks` (Types I/II),
`NonTrivalentValencyTwoTracks` (`2 + 2`), `NonTrivalentValencyTwoTracksLeaf`
(`1 + 3` / `3 + 1`), `NonTrivalentValencyTwoBaseOneTracks` (Base I) and
`NonTrivalentValencyFourTracks`; the star equality (`hIncidence`) is then
supplied by their star-count companions `NonTrivalentValencyThreeStarCount`,
`NonTrivalentValencyThreeSimpleStarCount`, `NonTrivalentValencyTwoStarCount` /
`NonTrivalentValencyTwoStarCountAll`, `NonTrivalentValencyTwoBaseOneStarCount`
and `NonTrivalentValencyFourStarCount`.  `data.Connected`,
`∀ v, nonDanglingValency data v ≤ 3` and `HasPathEnds data` remain explicit
hypotheses of every constructor, exactly as in `StableSourceDarts.ofDatum`.
The declarations of `StableGraphIncidence`, `StableSourceDartsTransport` and
`Utilities/CubicGraphs/CubicDarts.lean` are used as they stand.

## Consumers

`tracksOfMovedIncidence` is called directly by the vertex-half `tracks` files
at each valency: `NonTrivalentValencyThreeTracks` (Type III),
`NonTrivalentValencyThreeSimpleTracks` (Types I/II),
`NonTrivalentValencyTwoTracks` (`2 + 2`), `NonTrivalentValencyTwoTracksLeaf`
(`1 + 3` / `3 + 1`), `NonTrivalentValencyTwoBaseOneTracks` (Base I) and
`NonTrivalentValencyFourTracks`.  Through them it supplies the `tracks` field
of `OuterWalk.TypeChangeLink` at every non-trivalent wall, consumed by
`NonTrivalentValencyThreeExit`, `NonTrivalentValencyThreeSimpleExit`,
`NonTrivalentValencyTwoExit` / `NonTrivalentValencyTwoExitFree`,
`NonTrivalentValencyTwoBaseOneExit` and `NonTrivalentValencyFourExitLink`.
-/

namespace DraismaVargas.LocalCases.MovedIncidenceIso

open DraismaVargas.Infrastructure W4StableSource StablePathCount StableGraphIncidence
open CubicDarts CubicDartGraph StableSourceDarts

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **An incidence dictionary onto an arbitrary cubic dart graph.**  The branch
vertices of `data` are identified with the vertices of `H`, every dart of `H`
carries a stable row of `data` that is constant on the edges of `H`, and the
row-filtered stars agree.  Compare `StableGraphIncidence.Equivalence`, whose
second argument is a second gluing datum; here the second object is a bare
cubic dart graph, so the row bijection is replaced by a label on darts. -/
structure DatumGraphIncidence (H : CubicDartGraph D V) where
  /-- the branch vertices of the cover are the vertices of `H` -/
  vertex : BranchVertex data ≃ V
  /-- the stable row of `data` carried by a dart of `H` -/
  rowLabel : D → StablePath data
  /-- the two darts of an edge of `H` carry the same row -/
  rowLabel_op : ∀ d : D, rowLabel (H.op d) = rowLabel d
  /-- each row-filtered star of the cover has as many occurrences as the
  corresponding star of `H` has darts -/
  incidence : ∀ (v : BranchVertex data) (r : StablePath data),
    incidenceCount data v.1 r = Nat.card {d : D // H.vert d = vertex v ∧ rowLabel d = r}

namespace DatumGraphIncidence

variable {data} {H : CubicDartGraph D V}

/-- Group the darts of `H` by their vertex and their row. -/
def flagEquiv (certificate : DatumGraphIncidence data H) :
    D ≃ Σ x : V, Σ r : StablePath data,
      {d : D // H.vert d = x ∧ certificate.rowLabel d = r} where
  toFun d := ⟨H.vert d, certificate.rowLabel d, ⟨d, rfl, rfl⟩⟩
  invFun d := d.2.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, r, d, hx, hr⟩
    cases hx
    cases hr
    rfl

/-- Only inside one fixed branch/row star is a finite bijection chosen; both
labels are prescribed by the dictionary. -/
noncomputable def fibreEquiv (certificate : DatumGraphIncidence data H)
    (v : BranchVertex data) (r : StablePath data) :
    {e : NonDanglingEdge data // Incident data e.1 v.1 ∧ e.stablePath = r} ≃
      {d : D // H.vert d = certificate.vertex v ∧ certificate.rowLabel d = r} := by
  classical
  apply Fintype.equivOfCardEq
  rw [card_incidence, certificate.incidence v r, Nat.card_eq_fintype_card]

/-- The dart bijection: the dictionary's branch and row data, with one chosen
bijection inside each star. -/
noncomputable def dartEquiv (certificate : DatumGraphIncidence data H) : Dart data ≃ D :=
  (StableSourceDarts.flagEquiv data).trans
    ((Equiv.sigmaCongr certificate.vertex fun v ↦
      Equiv.sigmaCongr (Equiv.refl (StablePath data)) (fibreEquiv certificate v)).trans
      (flagEquiv certificate).symm)

theorem vert_dartEquiv (certificate : DatumGraphIncidence data H) (d : Dart data) :
    H.vert (certificate.dartEquiv d) = certificate.vertex (StableSourceDarts.vertex data d) :=
  (fibreEquiv certificate d.1 (row data d) ⟨d.2.1, d.2.2, rfl⟩).2.1

theorem rowLabel_dartEquiv (certificate : DatumGraphIncidence data H) (d : Dart data) :
    certificate.rowLabel (certificate.dartEquiv d) = row data d :=
  (fibreEquiv certificate d.1 (row data d) ⟨d.2.1, d.2.2, rfl⟩).2.2

/-- **The edge involution is determined, not assumed.**  In the constructed
stable graph the opposite dart is the unique other dart of the same row, so
`rowLabel_op` together with `H.op_ne` forces `H.op` to agree with it. -/
theorem op_dartEquiv (certificate : DatumGraphIncidence data H)
    (hConnected : data.Connected) (hEnds : HasPathEnds data) (d : Dart data) :
    H.op (certificate.dartEquiv d) =
      certificate.dartEquiv (opposite data hConnected hEnds d) := by
  have hApply : certificate.dartEquiv
      (certificate.dartEquiv.symm (H.op (certificate.dartEquiv d)))
      = H.op (certificate.dartEquiv d) := Equiv.apply_symm_apply _ _
  have hRow : row data (certificate.dartEquiv.symm (H.op (certificate.dartEquiv d)))
      = row data d := by
    rw [← rowLabel_dartEquiv certificate, hApply, certificate.rowLabel_op,
      rowLabel_dartEquiv certificate]
  have hNe : certificate.dartEquiv.symm (H.op (certificate.dartEquiv d)) ≠ d := by
    intro hEq
    rw [hEq] at hApply
    exact H.op_ne (certificate.dartEquiv d) hApply.symm
  have hOpp : certificate.dartEquiv.symm (H.op (certificate.dartEquiv d))
      = opposite data hConnected hEnds d :=
    opposite_eq_of_row_eq data hConnected hEnds hRow hNe
  rw [← hOpp, Equiv.apply_symm_apply]

end DatumGraphIncidence

/-- **The constructor.**  A multiplicity-preserving incidence dictionary onto an
arbitrary cubic dart graph gives an actual isomorphism from the cover's stable
graph, including rows whose two ends sit at the same branch vertex. -/
noncomputable def isoOfDatumGraphIncidence {H : CubicDartGraph D V}
    (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (hEnds : HasPathEnds data) (certificate : DatumGraphIncidence data H) :
    Iso (ofDatum data hConnected hTrivalent hEnds) H where
  dart := certificate.dartEquiv
  vtx := certificate.vertex
  op_map d := certificate.op_dartEquiv hConnected hEnds d
  vert_map d := certificate.vert_dartEquiv d

@[simp] theorem isoOfDatumGraphIncidence_dart {H : CubicDartGraph D V}
    (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (hEnds : HasPathEnds data) (certificate : DatumGraphIncidence data H) :
    (isoOfDatumGraphIncidence data hConnected hTrivalent hEnds certificate).dart =
      certificate.dartEquiv := rfl

@[simp] theorem isoOfDatumGraphIncidence_vtx {H : CubicDartGraph D V}
    (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (hEnds : HasPathEnds data) (certificate : DatumGraphIncidence data H) :
    (isoOfDatumGraphIncidence data hConnected hTrivalent hEnds certificate).vtx =
      certificate.vertex := rfl

/-! ### The moved target -/

section Move

variable (G : CubicDartGraph D V) (m₀ : G.MoveData)

/-- The incidence dictionary onto `G.move m₀`, spelled out: the involution is
`G.op` and the vertex map is the permuted one. -/
noncomputable def movedIncidence (vertexEquiv : BranchVertex data ≃ V)
    (rowLabel : D → StablePath data) (hOp : ∀ d : D, rowLabel (G.op d) = rowLabel d)
    (hIncidence : ∀ (v : BranchVertex data) (r : StablePath data),
      incidenceCount data v.1 r =
        Nat.card {d : D // G.vert (m₀.perm d) = vertexEquiv v ∧ rowLabel d = r}) :
    DatumGraphIncidence data (G.move m₀) where
  vertex := vertexEquiv
  rowLabel := rowLabel
  rowLabel_op := hOp
  incidence := hIncidence

/-- **The moved-target constructor.**  This is the `iso` half of
`InteriorGraphTracking.Tracks fd (graph.move m) label`: the target is the
literal Whitehead move of the tracked ambient graph, and the input is a
branch-vertex bijection together with a row label whose stars are counted
against the *permuted* vertex map. -/
noncomputable def isoOfMovedIncidenceEquivalence
    (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (hEnds : HasPathEnds data) (vertexEquiv : BranchVertex data ≃ V)
    (rowLabel : D → StablePath data) (hOp : ∀ d : D, rowLabel (G.op d) = rowLabel d)
    (hIncidence : ∀ (v : BranchVertex data) (r : StablePath data),
      incidenceCount data v.1 r =
        Nat.card {d : D // G.vert (m₀.perm d) = vertexEquiv v ∧ rowLabel d = r}) :
    Iso (ofDatum data hConnected hTrivalent hEnds) (G.move m₀) :=
  isoOfDatumGraphIncidence data hConnected hTrivalent hEnds
    (movedIncidence data G m₀ vertexEquiv rowLabel hOp hIncidence)

theorem rowLabel_isoOfMovedIncidenceEquivalence
    (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (hEnds : HasPathEnds data) (vertexEquiv : BranchVertex data ≃ V)
    (rowLabel : D → StablePath data) (hOp : ∀ d : D, rowLabel (G.op d) = rowLabel d)
    (hIncidence : ∀ (v : BranchVertex data) (r : StablePath data),
      incidenceCount data v.1 r =
        Nat.card {d : D // G.vert (m₀.perm d) = vertexEquiv v ∧ rowLabel d = r})
    (d : Dart data) :
    rowLabel ((isoOfMovedIncidenceEquivalence data G m₀ hConnected hTrivalent hEnds
      vertexEquiv rowLabel hOp hIncidence).dart d) = row data d :=
  DatumGraphIncidence.rowLabel_dartEquiv
    (movedIncidence data G m₀ vertexEquiv rowLabel hOp hIncidence) d

end Move

/-! ### The packaged tracking datum -/

section Tracks

open FullDimensionalSource

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The `Tracks` obligation of a type-change exit, from incidence data
alone.**  Taking the row label to be the chart coordinate read backwards makes
`row_map` hold by construction, so only the branch-vertex bijection and the
star count are left to the geometry. -/
noncomputable def tracksOfMovedIncidence
    (fd : FullDimensionalSourcePresentation data coordinate)
    (G : CubicDartGraph D V) (m₀ : G.MoveData) (label : D → coordinate)
    (vertexEquiv : BranchVertex data ≃ V)
    (hOp : ∀ d : D, label (G.op d) = label d)
    (hIncidence : ∀ (v : BranchVertex data) (r : StablePath data),
      incidenceCount data v.1 r =
        Nat.card {d : D // G.vert (m₀.perm d) = vertexEquiv v ∧
          label d = fd.labelling.row r}) :
    InteriorGraphTracking.Tracks fd (G.move m₀) label where
  iso := isoOfMovedIncidenceEquivalence data G m₀ fd.connected fd.trivalent fd.pathEnds
    vertexEquiv (fun d ↦ fd.labelling.row.symm (label d))
    (fun d ↦ by rw [hOp]) (fun v r ↦ by
      rw [hIncidence v r]
      exact congrArg Nat.card (congrArg _ (funext fun d ↦ by
        rw [Equiv.symm_apply_eq])))
  row_map d := by
    have hRow := rowLabel_isoOfMovedIncidenceEquivalence data G m₀ fd.connected fd.trivalent
      fd.pathEnds vertexEquiv (fun d ↦ fd.labelling.row.symm (label d))
      (fun d ↦ by rw [hOp]) (fun v r ↦ by
        rw [hIncidence v r]
        exact congrArg Nat.card (congrArg _ (funext fun d ↦ by
          rw [Equiv.symm_apply_eq]))) d
    rw [← hRow, Equiv.apply_symm_apply]

/-- **The tracked label is constant on the edges of the tracked graph.**  This
is the `hOp` hypothesis of `tracksOfMovedIncidence`, and it is free: the label of
a dart is the chart coordinate of its stable row, and the two darts of an edge of
the stable graph carry the same row.  A Whitehead move does not change `op`, so
the same statement holds for `G.move m₀`. -/
theorem label_op_of_tracks (fd : FullDimensionalSourcePresentation data coordinate)
    {H : CubicDartGraph D V} {label : D → coordinate}
    (tracking : InteriorGraphTracking.Tracks fd H label) (d : D) :
    label (H.op d) = label d := by
  have hApply : tracking.iso.dart (tracking.iso.dart.symm d) = d := Equiv.apply_symm_apply _ _
  have hOp : H.op (tracking.iso.dart (tracking.iso.dart.symm d)) = tracking.iso.dart
      (opposite data fd.connected fd.pathEnds (tracking.iso.dart.symm d)) :=
    tracking.iso.op_map _
  rw [hApply] at hOp
  rw [hOp, tracking.row_map, row_opposite, ← tracking.row_map (tracking.iso.dart.symm d), hApply]

end Tracks


/-! ### Non-vacuity -/

/-- The star of a branch vertex on one row, counted in the constructed dart
graph's own darts. -/
theorem card_fibre_ofDatum (v : BranchVertex data) (r : StablePath data) :
    Nat.card {d : Dart data // StableSourceDarts.vertex data d = v ∧ row data d = r} =
      incidenceCount data v.1 r := by
  classical
  have hEquiv : {d : Dart data // StableSourceDarts.vertex data d = v ∧ row data d = r} ≃
      {e : NonDanglingEdge data // Incident data e.1 v.1 ∧ e.stablePath = r} :=
    { toFun := fun d ↦ ⟨d.1.2.1, by
        obtain ⟨⟨w, e⟩, hw, hr⟩ := d
        cases hw
        exact ⟨e.2, hr⟩⟩
      invFun := fun e ↦ ⟨⟨v, ⟨e.1, e.2.1⟩⟩, rfl, e.2.2⟩
      left_inv := by
        rintro ⟨⟨w, e⟩, hw, hr⟩
        cases hw
        rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr hEquiv, Nat.card_eq_fintype_card]
  exact card_incidence data v r

/-- **Non-vacuity.**  Every cover's own stable graph carries the identity
incidence dictionary, with the literal occurrence row labels. -/
noncomputable def DatumGraphIncidence.self (hConnected : data.Connected)
    (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3) (hEnds : HasPathEnds data) :
    DatumGraphIncidence data (ofDatum data hConnected hTrivalent hEnds) where
  vertex := Equiv.refl (BranchVertex data)
  rowLabel := row data
  rowLabel_op := row_opposite data hConnected hEnds
  incidence v r := (card_fibre_ofDatum data v r).symm

/-- Any isomorphism onto `H` is an incidence dictionary onto `H`, so the notion
is exactly as strong as an isomorphism. -/
noncomputable def DatumGraphIncidence.ofIso {H : CubicDartGraph D V}
    (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (hEnds : HasPathEnds data) (i : Iso (ofDatum data hConnected hTrivalent hEnds) H) :
    DatumGraphIncidence data H where
  vertex := i.vtx
  rowLabel d := row data (i.dart.symm d)
  rowLabel_op d := by
    have hOpp : i.dart.symm (H.op d) =
        opposite data hConnected hEnds (i.dart.symm d) := by
      apply i.dart.injective
      rw [Equiv.apply_symm_apply]
      have h := i.op_map (i.dart.symm d)
      rw [Equiv.apply_symm_apply] at h
      exact h
    rw [hOpp]
    exact row_opposite data hConnected hEnds _
  incidence v r := by
    rw [← card_fibre_ofDatum data v r]
    refine Nat.card_congr (Equiv.subtypeEquiv i.dart fun d ↦ ?_)
    constructor
    · rintro ⟨hv, hr⟩
      refine ⟨?_, ?_⟩
      · rw [i.vert_map d]
        exact congrArg i.vtx hv
      · rw [Equiv.symm_apply_apply]
        exact hr
    · rintro ⟨hv, hr⟩
      refine ⟨?_, ?_⟩
      · exact i.vtx.injective ((i.vert_map d).symm.trans hv)
      · rw [Equiv.symm_apply_apply] at hr
        exact hr

end DraismaVargas.LocalCases.MovedIncidenceIso
