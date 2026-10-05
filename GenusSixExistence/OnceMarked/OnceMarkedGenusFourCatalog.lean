module

/- Generated data, not written by hand: one route for each partition of size at most four,
   in the grammar of `OnceMarkedCatalog`. `OnceMarkedLowGenus` checks what each route means. -/

public import GenusSixExistence.OnceMarked.OnceMarkedCatalog

@[expose] public section

namespace MarkedGraphs.Generated.OnceMarkedGenusFourCatalog


open MarkedGraphs.OnceMarkedCatalog

def entries : List Entry := [
  { rows := [], route := .empty },
  { rows := [1], route := .hook },
  { rows := [2], route := .hook },
  { rows := [3], route := .hook },
  { rows := [2, 1], route := .hook },
  { rows := [4], route := .hook },
  { rows := [3, 1], route := .hook },
  { rows := [2, 2], route := .square },
]

def expectedRepresentativeRows : List (List Nat) := [
  [],
  [1],
  [2],
  [3],
  [2, 1],
  [4],
  [3, 1],
  [2, 2],
]

def expectedRows : List (List Nat) := [
  [],
  [1],
  [2],
  [1, 1],
  [3],
  [2, 1],
  [1, 1, 1],
  [4],
  [3, 1],
  [2, 2],
  [2, 1, 1],
  [1, 1, 1, 1],
]

end MarkedGraphs.Generated.OnceMarkedGenusFourCatalog
