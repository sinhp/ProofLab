import tactic
import lectures.lec13_structures_on_gaussian_int


/- A __set__ `S` in `U` is just a predicate `S : U → Prop`  -/




/- If `U` is any type, the type `set U` consists of sets of elements of `U`.-/ 


/- `set U := U → Prop` -/

/-the set `univ`, which consists of all the elements of type `U`, and the empty set, `∅`, which can be typed as \empty.-/


/- For a set `S : set U` and `x : U` we write `x ∈ S` for the proposition `S x`. -/




variable {U : Type*}
variables (A B C D E : set U)

open set


#check ( { 0 } : set ℕ) 

-- The subset relation can be typed with \sub

#check A ⊆ B 
-- `A ⊆ B` is defined by the logical statement  `∀  x : U , (x ∈ A → x ∈ B)`



-- intersection can be typed with \i or \cap.
#check A ∩ B 

--Union can be typed with \un or \cup.
#check A ∪ B 


#check @mem_inter
#check @mem_of_mem_inter_left
#check @mem_of_mem_inter_right
#check @mem_union_left
#check @mem_union_right
#check @mem_or_mem_of_mem_union
#check @not_mem_empty


/-
Recall that `rw` is rewrite tactic which corresponds to the substitution.
-/

lemma subset_reflexivity : A ⊆ A := 
begin 
rw subset_def, 
intro x, 
intro h,
exact h, 
end   

lemma subset_transitivity {h₁ : A ⊆ B} {h₂ : B ⊆ C} : A ⊆ C 
:=
begin
intros x h₃,
rw subset_def at h₁, 
rw subset_def at h₂,
have h₄, from h₁ x, 
have h₅, from h₄ h₃,
exact h₂ x h₅,
end    

-- we can combine all intros into one step using `intros` instead of multiple instances of `intro`.

-- we can also combine `rw subset_def at h₁` and   `rw subset_def at h₂` together. 

example (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C 
:=
begin
rw subset_def, 
intros x h₃,
rw subset_def at h₁ h₂,  
have h₄, from h₁ x, 
have h₅, from h₄ h₃,
exact h₂ x h₅,
end 

/- 
Lean is smart and it lets us further simplify the proof above by deleting the calls to `rw` entirely. 
To do this, under the hood, Lean uses something called **definitional reduction**: to make sense of the `intros` command and the anonymous constructors Lean is forced to expand the definitions automatically so that we don't have to.
-/

-- We rewrite the proof above using definitional reduction: 

example (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C 
:=
begin
intros x h₃, 
have h₄, from h₁ h₃, 
show x ∈ C, from h₂ h₄,
end 



---------------------
--**Intersection**--
---------------------

/-
We can use the more concise notation `hx.1` and `hx.2` for `and.left hx` and `and.right hx`, respectively. Below is a proof with `hx.1` and `hx.2` instead of `and.left hx` and `and.right hx`.
-/

example (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
begin
  -- tactics are applied to goals
  rw subset_def, 
  -- ⊢ ∀ (x : U), x ∈ A ∩ C → x ∈ B ∩ C
  rw inter_def,
  -- ⊢ ∀ (x : U), x ∈ {a : U | a ∈ A ∧ a ∈ C} → x ∈ B ∩ C
  rw inter_def, 
  rw subset_def at h,
  dsimp,
  -- try to understand what `dsimp` does here for us
  intros x hx, 
  have hx_B, from h x hx.1, 
  show x ∈ B ∧ x ∈ C, from ⟨hx_B, hx.2⟩,  
end

/-
The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or some (non-dependent) hypotheses. It has many variants. A variant is called `dsimp` (definitional simp) and is similar to simp, except that it only uses definitional equalities.
-/

/- 
 Unlike `rw`, `simp` can perform simplifications inside a universal or existential quantifier. As usual, if you step through the proof, you can see the effects of these commands.
-/ 

/-
Let's reflect on what happened in the last three steps of the proof above: we introduced `hx: x ∈ A ∧ x ∈ C` then we destrctured it into `hx.1 :  x ∈ A` and `hx.2 : x ∈ C ` which then were used to construct a proof of `x ∈ B ∧ x ∈ C`.
The `rintro` combines the introducing and destrcturing in one tactic. `rintros` is an alias for rintro. Look at the penultimate line of the proof below to see a working example of `rintros`.
-/

example (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
begin
  -- tactics are applied to goals
  rw subset_def, 
  -- ⊢ ∀ (x : U), x ∈ A ∩ C → x ∈ B ∩ C
  rw inter_def,
  -- ⊢ ∀ (x : U), x ∈ {a : U | a ∈ A ∧ a ∈ C} → x ∈ B ∩ C
  rw inter_def, 
  rw subset_def at h,
  dsimp,
  rintros x ⟨xa, xc⟩,
  exact ⟨h x xa, xc⟩,
end


/-
 For brevity, we could package all `rw` tactics together as follows 
-/

example (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
begin
  rw [subset_def, inter_def, inter_def ],   
  rw subset_def at h,
  dsimp,
  -- what is dsimp doing here?
  rintros x ⟨xa, xc⟩,
  exact ⟨h _ xa, xc⟩,
end

/-
`simp only [h₁ h₂ ... hₙ]` is like `simp [h₁ h₂ ... hₙ]` but does not use `[simp]` lemmas
-/

-- Yet another shorter proof
example (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
begin
simp only [subset_def, mem_inter_eq] at * ,
rintros x ⟨h₁,h₂⟩,
exact ⟨h x h₁, h₂⟩,
end


---------------------
--**Union**---------
---------------------

/-
To deal with unions, we can use `set.union_def` and `set.mem_union`. Since `x ∈ s ∪ t` unfolds to `x ∈ s ∨ x ∈ t`, we can also use the cases tactic to force a definitional reduction.
-/

-- fill in `sorry` below. 
example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  intros x hx,
  cases hx.2 with hx₃ hx₄,
  { left,
    show x ∈ A ∩ B,
    exact ⟨hx.1, hx₃⟩ },
  right,
  show x ∈ A ∩ C,
  exact sorry,
end


example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
rw subset_def, 
intros x hx, 
rw union_def, 
dsimp, 
rw inter_def at hx, 
dsimp at hx, 
cases hx.2 with hx_3 hx_4, 
{ exact or.inl ⟨hx.1, hx_3⟩,   },
{exact or.inr ⟨hx.1, hx_4⟩},
end 


-- fill in `sorry` below.
example : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  rintros x ⟨hx_A, hx_B | hx_C⟩,
  { left, exact ⟨hx_A, hx_B⟩ },
  { sorry },
end


-- Let's prove the converse inclusion of sets: 
-- fill in `sorry` below.
example : (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C):=
sorry



/- 
To prove that two sets are equal, it suffices to show that every element of one is an element of the other. This principle is known as “extensionality” and, unsurprisingly, the `ext` tactic is equipped to handle it.
-/

-- To prove the operation of intersection is commutative we use the facts that the intersection is defined in term of conjunction and that conjunction is commutative. The latter was proved in the Lean Lab on propositional logic.



lemma conj_comm {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
begin
  split, 
  { intro h,
    cases h with hp hq,
    show Q ∧ P, from ⟨hq , hp⟩ 
  },
  {
    intro h,
    cases h with hq hp,
    show P ∧ Q, from ⟨hp , hq⟩ 
  }, 
end

-- we use the lemma above in the proof of commutativity of intersection.

example : A ∩ B = B ∩ A :=
begin
  ext x,
  simp only [mem_inter_eq],
  apply conj_comm,
end

-- The commutativity of conjunction is part of the Lean library where it is called `and.comm`; we invoke it in the short proof in below:

example : A ∩ B = B ∩ A :=
by ext x; simp [and.comm]


-- challenge: fill in the `sorry` below.
example : A ∪ B = B ∪ A :=
by ext x; simp sorry


-- We showed in the lecture on sets that if we prove A ⊆ B and B ⊆ A then it follows that A = B. This idea is implemented in Lean by the the theorem `subset.antisymm`. Here is a use of it:

example (h : A ⊆ B) : A ∪ B = B
:= 
begin
  apply subset.antisymm, 
  -- now we have 2 goals  A ∪ B ⊆ B and B ⊆ A ∪ B
  {
    rintros x (hx_A | hx_B), 
      {exact h hx_A},
      {exact hx_B},
  },
  {
    intros x hx_B,
    dsimp, 
    exact (or.inr hx_B),
  }, 
end 

-- when using `rintros`, sometimes we need to use parentheses around a disjunctive pattern `h₁ | h₂` to get Lean to parse it correctly.


example (h : A ⊆ B) : A ∩ B = A
:= 
begin
  sorry 
end 


example : A ∩ (A ∪ B) = A :=
sorry

example : A ∪ (A ∩ B) = A :=
sorry


------------------------
--**Relative Complement**
------------------------


/- 
The library also defines set difference `A \ B` (i.e. the complement of `B` relative to `A`), where the backslash is a special unicode character entered as `\\`. Recall that the expression `x ∈ A \ B` is by definition the same as `x ∈ A ∧ x ∉ B`. (The `∉` can be entered as `\notin`.) 
The operation of set difference is left-associative, that is  A \ B \ C reads as 
(A \ B) \ C. Therefore, 
x ∈ A \ B \ C ↔ (x ∈ A ∧ x ∉ B) ∧ x ∉ C  
-/

-- fill in the sorry below:
example : A \ B \ C ⊆ A \ (B ∪ C) :=
begin
  intros x h,
  have h₁ : x ∈ A := h.1.1,
  have h₂ : x ∉ B := h.1.2,
  have h₃ : x ∉ C := h.2,
  split,
  -- we now have two goals: x ∈ A and (λ (a : U), a ∉ B ∪ C) x. The latter is equivalent to x ∉ B ∪ C. 
  { exact h₁ }, 
  { dsimp,
  -- current goal: ¬(x ∈ B ∨ x ∈ C)
    intro h, -- x ∈ B ∨ x ∈ C
  cases h with h_B h_C,
  { show false, from h₂ h_B },
  show false, from sorry
  },
end

example : A \ B \ C ⊆ A \ (B ∪ C) :=
begin
  rintros x ⟨⟨h_A, hn_B⟩, hn_C⟩,
  use h_A,
  -- the tactic `use` instantiate the first term in a conjunctive goal. Since we want to prove x ∈ A \ (B ∪ C), `use h_A` will reduce the goal to x ∉ B ∪ C. 
  dsimp, 
  rintros (h_B | h_C); contradiction,
  --Here we sue the `contradiction` tactic to shorten the proof by letting Lean find in the current local context two contradictory hypotheses, for instance, h_B and hn_B.
end

-- Two sets A and B are called **disjoint** if A ∩ B = ∅. Theorem: We can write any union of two sets as a union of two disjoint sets. First we prove two lemmas: 

lemma disjoint_union_of_union_1 {A B : set U } : A ∪ (B \ A) ⊆ A ∪ B 
:= 
begin
  rw subset_def,  
  dsimp,  
  rintros x (h_A | h_B), 
  apply or.inl; exact h_A, 
  apply or.inr; exact h_B.1,
end 

-- fill in the sorry below

lemma disjoint_union_of_union_2 {A B : set U } :  A ∪ B ⊆ A ∪ (B \ A)
:= 
begin
  rw subset_def, 
  dsimp, 
  intros x hx, 
  cases hx, 
  { 
    exact or.inl hx
  },
  {
    cases em (x ∈ A),
    -- the use of LEM in here makes the proof non-constructive.
    exact or.inl h, 
    exact or.inr sorry,
  },
end 




/-
The theorem `subset.antisymm` is an alternative to using `ext`. It allows us to prove an equation A = B between sets by proving A ⊆ B and B ⊆ A.
-/
theorem disjoint_union_of_union {A B : set U } : A ∪ B = A ∪ (B \ A) 
:= 
begin
  apply subset.antisymm,
  apply disjoint_union_of_union_2, 
  apply disjoint_union_of_union_1,
end 


---------------------
--**Disjoint unions**
---------------------

/-
In below we define the sets of even and odd numbers and prove that they cover all natural numbers, i.e. their union is exactly the entire set of natural numbers. The proof below used LEM but there is a better constructive proof which uses division by 2 algorithm. 
-/

def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em,
end


/-
The union evens ∪ odds is indeed a disjoint union since evens ∩ odds = ∅. We want to prove a stronger theorem that the disjoint union of evens and odds is the whole of ℕ. 
-/


---------------------------------------
--**The empty set and the universal set**
---------------------------------------

/- 
The sets `∅` and `univ` are defined relative to the domain of discourse. For instance if the domain of discourse is natural numbers then `∅ : set ℕ` but if the domain of discourse is integers then `∅ : set ℤ`. 
-/

/-
We often need to indicate the type of `∅` and `univ` explicitly, because Lean cannot infer which ones we mean. The following examples show how Lean unfolds the last two definitions when needed. In the second one, `trivial` is the canonical proof of `true` in the library.
-/


example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

example (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial




-----------------------------------
--**Power set**
-----------------------------------

def power_set (A : set U) : set (set U) := {B : set U | B ⊆ A}

example (A B : set U) (h : B ∈ power_set A) : B ⊆ A :=
h

-- As the example shows, B ∈ powerset A is then definitionally the same as B ⊆ A.

example : A ∈ powerset (A ∪ B) :=
begin 
intros x _,
show x ∈ A ∪ B, from or.inl ‹x ∈ A›,
end   


-- powersets are part of the Lean core library. They are defined as above. Type "\power" to get 𝒫. 

#check 𝒫 A

#check A ⊆ B
#check 𝒫 A ⊆ 𝒫 B



-- we use the lemma subset_transitivity at the beginning of the file to prove the theorem belo
theorem subset_relation_lifts_to_power_sets {A B : set U} : (A ⊆ B) → (𝒫 A ⊆ 𝒫 B)  
:= 
begin
 intros h S hS,  
 apply subset_transitivity S A B,
 exact hS,
 exact h, 
end 



lemma singelton_of_element {A : set U} {x : U} : x ∈ A ↔  {x} ⊆ A := 
begin
  split, 
  { intro h,
    intros y hy, 
    simp at hy, 
    -- what is going on here? what does simp do?
    rw hy,
    exact h, 
    },
  {
    sorry,
  },  
end  


theorem subset_transport {A B : set U} {x : U} (A ⊆ B): 
(x ∈ A) → (x ∈ B)
:= 
begin 
  intro h, 
  exact H h, 
end 




-----------------------------------
--**Cartesian binrary product of sets**--
-----------------------------------


/- 
The ordered pair of two objects a and b is denoted (a, b). We say that a is the first component and b is the second component of the pair. 
-/

/-
We proved in class that two pairs are only equal if the first component are equal and the second components are equal. In symbols, (a, b) = (c, d) if and only if a = c and b = d.
-/

/-
We also defined for any given sets A and B, the cartesian product A × B of these two sets as the set of all pairs where the first component is an element in A and the second component is an element in B. In set-builder notation this means
`A × B = { (a, b) | a ∈ A ∧ b ∈ B }`.
-/

/- 
Note that, in contrast to intersections, unions, and (relative) complements, if `A B : set U` the set A × B need not be of the type `set U`. However, `A × B : set (U × U)`. 
-/

#check A × B 
#check set A × B

#check {p : A × B | (p.1 ∈ A) ∧ (p.2 ∈ B)} 

example {A B : set U} {a ∈ A} {b ∈ B} : 
(a,b) ∈ A ×ˢ B :=
begin
sorry, 
end 

-- this is not what we are looking! Instead we use the operation `×ˢ` to form the Cartesian binrary product of sets. Write ×ˢ by typing "\timesˢ" and then hit tab/space.

-- infix ` ×ˢ `:72 := has_set_prod.prod

namespace set

/-! ### Cartesian binary product of sets -/

section prod
variables {α β γ δ : Type*} {s s₁ s₂ : set α} {t t₁ t₂ : set β} {a : α} {b : β}

/- 
The cartesian product `A ×ˢ B` is the set of `(a, b)`
  such that `a ∈ A` and `b ∈ B`.
In the Lean core library this is defined as in below:
`instance : has_set_prod (set α) (set β) (set (α × β)) := ⟨λ s t, {p | p.1 ∈ s ∧ p.2 ∈ t}⟩`
-/


-- some useful theorems about cartesian product of sets
#check mem_prod_eq 
#check mem_prod 
#check prod_mk_mem_set_prod_eq 


-- Let's prove that the product of any set with the empty set is empty again. 

theorem product_with_empty_right {A : set U} : A ×ˢ (∅ : set U)=  ∅ 
:=
begin
ext, 
rw mem_prod_eq,
exact and_false _, 
end 

#check and_false
#check false_and

-- fill in the sorry below
theorem product_with_empty_left {A : set U} :  (∅ : set U) ×ˢ A =  ∅ 
:=
begin
ext, 
rw mem_prod_eq,
sorry, 
end 







#check subgroup








