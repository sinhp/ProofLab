/- 
Graphs 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec11_type_classes

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true



open PROOFS

open PROOFS.STR






/-!
### Graphs

A simple graph is specified by the following data: 
1. A type `V` of vertices 
2. An irreflexive symmetric binary predicate (i.e. relation) `adj` on `V` describing which pairs of vertices are adjacent. In other words, for vertices `v₁` and `v₂`, the proposition `adj v₁ v₂` expresses the condition for adjecency. 

- We want `adj` to be symmetric which is to say if vertex `v₁` is adjacent to vertex `v₂` then `v₂` is also adjacent to `v₁`.  
- We want `adj` to be irreflexive which is to say we do not want to have loops. 

The relation 
There is exactly one edge for every pair of adjacent vertices;
see `simple_graph.edge_set` for the corresponding edge set.


Given a type `V`, then `G : simple_graph V` is a simple graph defined over `V` with an adjacency relation `G.adj` between vertices of type V that is symmetric (G.sym) and irreflexive (G.noloop).
-/



@[ext]
structure simple_graph_str (V : Type) :=
(adj : V → V → Prop)
(symm : symmetric adj)
(noloop : irreflexive adj)


#check simple_graph_str

variable {X : Type}
variables {V : Type} (G : simple_graph_str V)



/-! ## Challenge
Define the __empty graph__ on a vertex type `V`, i.e. the graph with no edges on a given vertex type `V`.
 -/
def empty_graph_str (V : Type) : simple_graph_str V :=
{
  adj := λ v1 v2, false,
  symm := by
    {
      unfold symmetric,
      intros v1 v2,
      intro h,
      exact h,
    },
  noloop := by
    {
      unfold irreflexive,
      intro v1,
      intro h,
      exact h,
    },
}



/- 
### Challenge : 
Define a graph structure on the type `bool` where the only edge is between `ff` and `tt`. 
-/

def bool_graph_str : simple_graph_str bool :=
{
  adj := λ v1, λ v2, v1 ≠ v2,
  symm := by {rw symmetric,
              intros x y h₁,
              apply neq.symm,
              exact h₁},
  noloop := by {rw irreflexive,
                intros x h₁,
                have h₂ : x = x, by refl,
                exact neq.elim h₁ h₂,
                },
}





structure preorder_str (X : Type) := 
(rel : X → X → Prop)
(rflx : reflexive rel) 
(trns : transitive rel)


def preorder_bool : preorder_str bool := 
{
  rel := λ b, λ b', b && b' = b,
  rflx := by { unfold reflexive, -- 
               intro x, --   
               cases x, 
               repeat {refl}, 
               },
  trns := by { unfold transitive, 
               intros x y z, 
               intros h₁ h₂, rw ← h₁, rw bool_and_assoc, rw h₂}, 
}




/- 
### Challenge : 
Construct for any preorder a graph where there is an edge between any two points of the preorder if they are related to each other. 
-/
def graph_of_preorder_str (X : Type) (ρ : preorder_str X) : simple_graph_str (X) :=
{
  adj := λ x₁, λ x₂, (¬ ρ.rel x₁ x₂ ∧ ρ.rel x₂ x₁) ∨ (ρ.rel x₁ x₂ ∧ ¬ ρ.rel x₂ x₁),
  symm := by {
    unfold symmetric,
    intros x₁ x₂,
    intro h₁,
    cases h₁,
    {
      right,
      split,
      {
        exact h₁.2,
      },
      {
        exact h₁.1,
      },
    },
    {
      left,
      split,
      {
        exact h₁.2,
      },
      {
        exact h₁.1,
      }
    },
   },
  noloop := by {
    unfold irreflexive,
    intro x,
    intro h₁,
    cases h₁,
    {
      cases h₁ with hnr hr,
      exact hnr hr,
    },
    {
      cases h₁ with hr hnr,
      exact hnr hr,
    },
  }
}





/- 
### Challenge  : 
Construct the prodcut of two preorders. 
-/


def preorder_str.prod {X Y : Type} (P : preorder_str X) (Q : preorder_str Y) :
preorder_str (X × Y) :=
{
  rel := λ a, λ b, (P.rel a.1 b.1) ∧ (Q.rel a.2 b.2),
  rflx := by {unfold reflexive,
              intro q,
              split,
              {
                exact P.rflx q.fst,
              },
              {
                exact Q.rflx q.snd,
              },
              },
  trns := by {  unfold transitive,
                intros x y z,
                intro hpqx,
                intro hpqy,
                split,
                {
                  cases hpqx,
                  cases hpqy,
                  exact P.trns hpqx_left hpqy_left,
                },
                {
                  cases hpqx,
                  cases hpqy,
                  exact Q.trns hpqx_right hpqy_right,
                },},
}

/- 
### Challenge  : 
Construct the graph associated to the pointwise preorder on `bool × bool`. How many edges does this graph have?
-/

def graph_of_boolxbool_ptwise : simple_graph_str (bool × bool) := 
graph_of_preorder_str (bool × bool) (preorder_str.prod preorder_bool preorder_bool)





/-
### Challenge : 
Develope an API for simple graphs. 
-/


lemma adj_comm (u v : V) :
  G.adj u v ↔ G.adj v u :=
begin
  split,
  {
    intro h₁,
    exact G.symm h₁,
  },
  {
    intro h₁,
    exact G.symm h₁,
  },
end
  





/-  
### Challenge : 
The __complete graph__ on a type `V` is the simple graph with all pairs of distinct vertices adjacent.  
-/



def complete_graph_str (V : Type) : simple_graph_str V :=
{
  adj := λ x₁, λ x₂, ¬ (x₁ = x₂),
  symm := by {
    unfold symmetric,
    intros x₁ x₂,
    intro h₁,
    intro h₂,
    apply h₁,
    rw h₂,
  },
  noloop := by {
    unfold irreflexive,
    intro x,
    intro h₁,
    apply h₁,
    refl,
  },
}




/-
### Challenge : 
Define subgraphs. Suppose we have two graphs `G` and `H` on the same vertex type `V`. We say `G` is a subgraph of `H` if 
whenever any two vertex are connected by an edge in `G` they are connected by an edge in `H`. 
-/

def is_subgraph (G H : simple_graph_str V) : Prop := ∀ {x₁ x₂ : V}, (G.adj x₁ x₂ → H.adj x₁ x₂)



/-
### Challenge : 
Show that the empty graph is a subgraph of any other graph. 
-/

example (H : simple_graph_str V) : is_subgraph (empty_graph_str V) H :=
begin
unfold is_subgraph,
intros x₁ x₂ h₁,
exfalso,
exact h₁,
end




/- ### Challenge :
Show that every graph is a subgraph of the complete graph on the same vertex type. 
-/ 


lemma all_sub_of_comp (V : Type) (C G : simple_graph_str V) (h₁ : C = complete_graph_str V):
  is_subgraph G C :=
begin
  unfold is_subgraph,
  intros x₁ x₂,
  intro hg,
  rw h₁,
  intro hn,
  have hi : irreflexive G.adj, from G.noloop,
  rw hn at hg,
  unfold irreflexive at hi,
  exact (hi x₂) hg,
end






/-
### Challenge : 
Construct the sum of two graphs on the same type. The sum of two graphs `G` and `H` has an edge between two vertices if and only if either there is an edge between the same vertices in `G` or there is an edge between the same vertices in `H`. 
-/

@[simp]
def sum_of_graphs (G H : simple_graph_str V) : simple_graph_str V :=
{ adj := λ i j, G.adj i j ∨ H.adj i j,
  symm := by {unfold symmetric, intros x y, intro hGH, cases hGH,
              {
                left,
                apply G.symm hGH,
              },
              {
                right,
                apply H.symm hGH,
              },
            },
  noloop := by {unfold irreflexive, intros x h₁, cases h₁,
                {
                  have h₂: ¬G.adj x x, from G.noloop x,
                  apply h₂,
                  exact h₁,
                },
                {
                  have h₂: ¬H.adj x x, from H.noloop x,
                  apply h₂,
                  exact h₁,
                },
              },
}




/-
### Challenge : 
Define the __complement__ of a graph. The complement of a graph `G` is a graph `Gᶜ` on the same set of vertices as of G such that there will be an edge between two vertices `v₁` and `v₂` in G’, if and only if there is no edge in between `v₁` and `v₂` in `Gᶜ`.
-/
@[simp]
def complement (G : simple_graph_str V) : simple_graph_str V :=
{
  adj := λ v1, λ v2, (¬ G.adj v1 v2) ∧ v1 ≠ v2,

  symm := by
  {
    unfold symmetric,
    intros x y,
    intro h,
    split,
    {
      intro h1,
      have h2 := G.symm,
      have h3 := h2 h1,
      cases h,
      exact h_left h3,
    },
    {
      intro h1,
      cases h,
      have h2 : x = y := by rw h1,
      exact h_right h2,
      },
  },

  noloop := by
  {
    unfold irreflexive,
    intro v1,
    intro h,
    simp at *,
    exact h,
  },
}









/- ### Challenge :
Define the embedding of graphs. A __graph embedding__ is a injective function `f`  between the vertex types of two such that for vertices `v₁ v₂ : V`,
`G.adj f(v₁) f(v₂) ↔ G.adj v₁ v₂ `. 
-/


structure graph_embedding {V W : Type} (G : simple_graph_str V) (H : simple_graph_str W) := 
(to_fun : V → W) 
(to_fun_inj : is_injective to_fun)
(embed : ∀ {a b : V}, H.adj (to_fun a) (to_fun b) ↔ G.adj a b)



/- ### Challenge :
Show that an embedding with the identity function induces a subgraph. 
-/ 


/-
### Challenge : 
What is the sum of a graph of its complement. Prove it in Lean. 
-/

#check graph_embedding.to_fun

structure graph_isomorphism {V W : Type} (G : simple_graph_str V) (H : simple_graph_str W) extends graph_embedding G H := 
(surj : is_surjective to_fun)

#check graph_embedding
#check is_surjective




#check sum_of_graphs
#check complement

infix ` ≅ `:35 := graph_isomorphism 
def self_of_sum_complement_self {V : Type} {G : simple_graph_str V} : (sum_of_graphs G (complement G)) ≅ complete_graph_str V := 
{ to_fun := id,
  to_fun_inj := by {intros x y, simp,},
  embed := by {intros x y, simp, split, intro h, sorry, },
  surj := sorry, }


/- ### Challenge : 
A (proper) coloring of a graph `G` with color set `C` is a function `f : V → C` assigning colors to each vertex such that adjacent vertices have different colors. -/

structure colored_graph :=
(G : simple_graph_str V)
(C : Type)
(color : V → C)
(adj_diff_color : ∀ {v1 v2 : V}, G.adj v1 v2 → color v1 ≠ color v2)


/- ### Challenge : 
A bipartition of a graph `G` is a coloring of `G` with color set `{1,2}`. Let `V₁` and `V₂` respectively denote the color classes for colors 1 and 2. If a bipartition exists, the graph is called bipartite.
-/

structure bipartite_graph :=
(cgraph : colored_graph)
(color_1 : cgraph.C)
(color_2 : cgraph.C)
(two_colors : ∀ x : V, cgraph.color x = color_1 ∨ cgraph.color x = color_2)







