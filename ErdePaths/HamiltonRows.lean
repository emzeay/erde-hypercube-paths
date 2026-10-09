import ErdePaths.HamiltonScan

namespace ErdePaths.HamiltonRows
open HamiltonScan SquareLift

abbrev Edge := Vertex 2 × Vertex 2

def baseZero (q : Fin 4) : Edge :=
  match q.val with
  | 0 => (0,2)
  | 1 => (1,3)
  | 2 => (0,1)
  | _ => (2,3)

def baseLast (s : Bool) (q : Fin 4) : Edge :=
  if s then match q.val with
    | 0 => (0,2)
    | 1 => (2,3)
    | 2 => (0,1)
    | _ => (1,3)
  else match q.val with
    | 0 => (0,1)
    | 1 => (2,3)
    | 2 => (0,2)
    | _ => (1,3)

def lower (s : Bool) (q : Fin 4) : Edge :=
  match q.val with
  | 0 => (3,rowIndex (.primary s))
  | 1 => (0,rowIndex (.primary (!s)))
  | 2 => (rowIndex (.primary (!s)),3)
  | _ => (rowIndex (.primary s),0)

def upper (s : Bool) (q : Fin 4) : Edge :=
  match q.val with
  | 0 => (3,rowIndex (.primary (!s)))
  | 1 => (0,rowIndex (.primary s))
  | 2 => (0,rowIndex (.primary (!s)))
  | _ => (3,rowIndex (.primary s))

/-- Four distinct row edges with their actual undirected cube adjacency. -/
def Ledger (E : Fin 4→Edge) : Prop :=
  (∀q, Adjacent (E q).1 (E q).2) ∧
  (∀u v : Vertex 2, Adjacent u v → ∃q, SameEdge (E q) (u,v)) ∧
  (∀p q, SameEdge (E p) (E q) → p=q)

theorem baseZero_ledger : Ledger baseZero := by
  simp only [Ledger,SameEdge]
  decide

theorem baseLast_ledger : ∀s, Ledger (baseLast s) := by
  simp only [Ledger,SameEdge]
  decide

theorem lower_ledger : ∀s, Ledger (lower s) := by
  simp only [Ledger,SameEdge]
  decide

theorem upper_ledger : ∀s, Ledger (upper s) := by
  simp only [Ledger,SameEdge]
  decide

#print axioms baseZero_ledger
#print axioms lower_ledger
end ErdePaths.HamiltonRows
