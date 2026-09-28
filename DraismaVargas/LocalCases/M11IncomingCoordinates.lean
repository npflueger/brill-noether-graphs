import DraismaVargas.LocalCases.M11CommonBalance
import DraismaVargas.Infrastructure.GluingTransport

/-!
# Literal incoming columns at an M11 contraction

The actual contraction's old-or-new column equivalence, `incomingColumnEquiv`,
is proved here; the incoming-member identifications of the local cases read
their `Option` column dictionary through it.  The final definition,
`IncomingMatchingConclusion`, lists what an incoming-cover reconstruction in
case M-11 has to output; it is a specification, not an existence theorem.
-/

namespace DraismaVargas.LocalCases.M11IncomingCoordinates

open DraismaVargas.Infrastructure GraphContraction GluingContraction W4StableSource

variable {target : CFGraph} {a b : target.V} {contracted : target.edges}

/-- Literal incoming target columns: restore the contracted occurrence at
`none`, and use the already proved unfolding map at every retained column. -/
noncomputable def incomingColumnEquiv
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Option (contract target hab hOne).edges ≃ target.edges := by
  classical
  exact (Equiv.optionCongr (foldEdgeEquiv hc hab hOne).symm).trans
    (Equiv.optionSubtypeNe contracted)

@[simp] theorem incomingColumnEquiv_none
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    incomingColumnEquiv hc hab hOne none = contracted := rfl

@[simp] theorem incomingColumnEquiv_some
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (edge : (contract target hab hOne).edges) :
    incomingColumnEquiv hc hab hOne (some edge) = unfoldEdge hc hab hOne edge := rfl

@[simp] theorem incomingColumnEquiv_symm_contracted
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (incomingColumnEquiv hc hab hOne).symm contracted = none :=
  (incomingColumnEquiv hc hab hOne).symm_apply_eq.mpr rfl

/-- The output an incoming-cover reconstruction in case M-11 has to provide; a
specification, not an existence theorem. It records actual cover isomorphism,
the precise contracted column, the induced wall-row map, and every natural
matrix entry. -/
def IncomingMatchingConclusion {degree : ℕ} (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hCompat : WallDegeneration.DanglingCompatible incoming hc hab hOne)
    {star : W2R1Target.TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : SecondEquation.W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : W4Assembly.WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard block.1 = 2) : Prop :=
  ∃ position : Fin 3,
    let member := M11RemoteCandidates.candidates input profile hCard position
    ∃ targetIso : Utilities.CFGraphIso target member.outgoingTarget,
    ∃ sheets : (GluingTransport.transport targetIso incoming).SheetRelabeling,
      sheets.apply = member.datum ∧
      (∀ column : Option (contract target hab hOne).edges,
        GluingTransport.edgeEquiv targetIso (incomingColumnEquiv hc hab hOne column) =
          M11CommonBalance.columnEquiv input profile hCard position column) ∧
      ∃ rows : StablePath incoming ≃ StablePath member.datum,
        (∀ edge : NonDanglingEdge (contractDatum incoming hc hab hOne),
          rows (WallDegeneration.nonDanglingEmbedding incoming hCompat.1 edge).stablePath =
            M11CommonBalance.rowEquiv input profile hCard position edge.stablePath) ∧
        (∀ path : StablePath incoming, ∀ edge : target.edges,
          StableSourceMatrix.matrix incoming path edge =
            StableSourceMatrix.matrix member.datum (rows path)
              (GluingTransport.edgeEquiv targetIso edge))

end DraismaVargas.LocalCases.M11IncomingCoordinates
