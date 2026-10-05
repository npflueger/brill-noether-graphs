module

@[expose] public section

/-!
# Handwritten data grammar for once-marked finite catalogs

External generators may instantiate these types, but do not define their own
command or proof language.  The mathematical interpretation of each route is
checked in `OnceMarkedLowGenus.lean`.
-/

namespace MarkedGraphs.OnceMarkedCatalog


/-- The handwritten finite set of mathematical routes understood by the
once-marked low-genus checker. -/
inductive Route where
  | empty
  | hook
  | square
  deriving DecidableEq, Repr

/-- One passive catalog record: partition rows and a proposed route tag. -/
structure Entry where
  rows : List Nat
  route : Route
  deriving DecidableEq, Repr

end MarkedGraphs.OnceMarkedCatalog
