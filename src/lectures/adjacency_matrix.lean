import ..prooflab
import ..lectures.graph_contest
import ..lectures.lec11_type_classes
import lectures.lec8_structure_bundled
import lectures.lec9_structure_unbundled
import data.matrix.notation
import linear_algebra.matrix.determinant
import data.real.basic


namespace PROOFS

-- adjacency matrices

@[ext]
structure bool_graph_str (V : Type) :=
(adj : V → V → (bool))
(symm : ∀ v₁ v₂ : V, adj v₁ v₂ = adj v₂ v₁)
(noloop : ∀ v : V, adj v v = ff)


#check fin 1

@[ext]
structure binary_graph_str (V : Type) :=
(adj : V → V → fin 1)
(symm : ∀ v₁ v₂ : V, adj v₁ v₂ = adj v₂ v₁)
(noloop : ∀ v : V, adj v v = 0)

def bool_graph_to_binary_graph (V : Type) (G : bool_graph_str V) : binary_graph_str V :=
{
  adj := λ v₁, λ v₂, nat_of_bool (G.adj v₁ v₂),
  symm := by {intros v₁ v₂, rw G.symm},
  noloop := by {intro v, rw G.noloop, refl},
}

def binary_graph_to_bool_graph (V : Type) (G : binary_graph_str V) : bool_graph_str V :=
{
  adj := λ v₁, λ v₂, bool_of_nat (G.adj v₁ v₂),
  symm := by {intros v₁ v₂, rw G.symm},
  noloop := by {intro v, rw G.noloop, refl},
}

def graph_to_adj_mat (n : ℕ) (G : binary_graph_str (fin n)) : matrix (fin n) (fin n) (fin 1) :=
  matrix.of (λ m, λ n, G.adj m n)


def adj_mat_to_graph (n : ℕ) (M : matrix (fin n) (fin n) (fin 1)) (sym : ∀ i j : fin n, M i j = M j i) (nol : ∀ i : fin n, M i i = 0) : binary_graph_str (fin n) :=
{
  adj := λ i, λ j, M i j,
  symm := by {apply sym},
  noloop := by {apply nol},
}

-- multiplication of adjacenency matrices

def mat_to_sq_mat :=
λ (n : ℕ), λ (M : matrix (fin n) (fin n) (fin 1)), M.mul M



variable V : Type

variables (G : simple_graph_str V) [decidable_rel G.adj]
variables (α : Type)

def adj_matrix [has_zero α] [has_one α] : matrix V V α
| i j := if (G.adj i j) then 1 else 0

#check adj_matrix


#check fin 
#check finset -- multilist with no no duplicates
#print finset 
#check finset (fin 2)
#reduce finset (fin 2)
#reduce (fin 1)

#check fintype



#check matrix

#check num
#check cardinal

#check fintype.card

#check (fin 2).card 


#check fintype.card (fin 2)

#eval fintype.card (fin 2)

#eval fintype.card (fin 1) -- 1

#check transpose

end PROOFS

 