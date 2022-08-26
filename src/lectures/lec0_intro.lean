/- 
Basic Arithmetic With Tactics
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/
import ..prooflab

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true

/-
In this lesson, we learn the very basics of the language of Lean, and how to write some mathematical statements and their proofs in Lean.

We also learn about tactics and how to write some trivial proofs using the following tactics: 
1. refl 
2. exact 
-/

namespace PROOFS






/-! # What is Lean 

Lean is a functional programming language that makes it easy to write correct and maintainable code. We use Lean as an __interactive theorem prover__. 
  - Lean helps us prove the __correctness__ of mathematical statements, 
  - Lean lets us develop __automation__ to support __mathematical reasoning__ and __proof__.

At its core, Lean is what is known as a __type checker__. This means that we can write expressions and ask the system to check that they are well formed, and also ask the system to tell us what type of object they denote. 
  - Lean parses input, interpret it as expressions in a formal logical language, and
  - Lean determine the types of these formal expressions. 
-/





/-! ## Types (Collections)
In Lean things are largely organized as __types__ (collections) and __terms__ (elements). __In Lean every expression is typed__.  You can use the `#check` command to print its type.

Some familiar number systems such as __natural numbers (ℕ)__ , __integers (ℤ)__, __rational numbers (ℚ)__, and __real numbers (ℝ)__ are encoded as types in Lean. (Lean's "check" command tells us the type of the object we have constructd). 
-/

#check ℕ 
#check ℤ 
#check ℚ 
#check ℝ 

-- All types, except the __empty__ type, have terms (or elements, or inhabitants). For instance `0 : ℕ`. We read the expression `a : A` as `a is an A`. So `0 : ℕ` says `0 is a natural number`, and `0 : ℤ` says that `0 is an integer`. 

section -- `section` declares an environment 
#check bool -- the type of booleans
#check tt
#check ff 
 

#check 0
#check (0 : ℤ)
#check 2 + 2


#check [1, 2, 3] -- bracket notation for lists 
#check (1, 2, 3) -- round brackets for tuples
#check λ x, x + 1
end 

section -- we use `sections` to limit the __scope__ of a variable. Whatever variable we introduce in between `section ... end` remains hidden from the rest of the file. 
#check 2 + 2
set_option pp.all true
#check 2 + 2
end



/- 
We can introduce new types as follows: 
-/
variable A : Type
variables B C X Y Z U V W : Type
 
/- 
We do not know anything about types `A .... W` excepts that they are types. We don't even know if they have any terms. 

Note that the variables `A ... W` are global variables which means they are accessible throughout the entire file, and any file which imports this file. 
-/






/-! ### New Types from the Old -/

section 
#check A × B -- the type of pairs 
#check A ⊕ B  -- the sum type 
#check A → B -- the type of functions which we talk about in the lecture 
#check list A
end 


-- Some new types out of the type of natural numbers
section
#check ℕ × ℕ  
#check list ℕ
#check ℕ → list (ℕ × ℕ)
end 






/-! ### Propositions
- Some Lean expression are __propositions__, i.e. assertions that can be judged to be true or false. For instance `2 + 2 = 5` is a proposition. 
- Propositions are terms of type `Prop`. Here are some examples:
-/

section
#check 2 + 2 = 4
#check 2 + 2 = 5
#check ∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n
end 

/- 
We introduce a proposition by the expression `P : Prop`. 
-/
section 
variables P Q : Prop 
#check P 
#check P ∧ Q
#check P ∨ Q
#check P → Q
#check P ↔ Q
end 

/- 
For `P : Prop`, we read `hp : P` as "hp is a proof of P", or we have a hypothesis "P" verified by "hp", or "P is true by virtue of hp". 
-/
section
#check (rfl : 2 + 2 = 4) --rfl refers to "reflexivity"
#check rfl  
#check @rfl
#check (add_comm : ∀ x y : ℤ, x + y = y + x)
end


/- 
The term `rfl` is the (trivial) proof that any term is equal to itself. Here is a term-style proof of ` 2 = 2 `. Here `2 = 2` is the statement we wanna prove and `rfl` is the proof of it. 
-/

/-
To assert a statement in Lean we use the `example` environment which includes 
- context: the parameters which are used in the statement of the lemma. Think of context as a way of telling to Lean "let x, y, z, and n be natural numbers". A statement only makes sense in an appropriate context. 
- statement we wanna prove 
- the proof of the statement (which comes it two styles: term style and tactic style). 

A genral __term style__ form of an `example` is as follows: 

example (context_of_our_assumptions) : 
  statement_of_lemma := 
proof_of_lemma
-/

-- in the example below the context is empty. 
example : 
  2 = 2 := 
rfl 

-- An assertion can have a nonempty __context__: in below the context comprises of four variables of natural numbers `a b c d`. The statement we wanna prove tis that `(a + b) * (c + d) = (a + b) * (c + d)` and the proof is by reflexivity. 
example (a b c d : ℕ) : (a + b) * (c + d) = (a + b) * (c + d) := rfl


-- The term `rfl` proves more than syntactic equalities, it proves the equalities between terms which are __definitionally equal__. 
example : 2 + 3 = 5 := rfl 

-- `( ( ) ( ) ) ( ( ) ( ) ( ) ) = ( ( ) ( ) ( ) ( ) ( ) )`




/-! ## Tactics 
- There is another way of writing of proofs which is closer to how mathematicians write their proofs in maths books and journal papers. For instance, you might have seen a proof being written in the following style: "To prove the _forward direction_, first _unfold_ the definition. Suppose `x` is an arbitray blah which satisfy the property blah blah. By definition there is some `y` which satisfies the property blah blah blah. Now, _apply_ the previous lemma to `y`, and _specialize_ the result to when `y` is `y₀`."

- These are __instructions__ given by the author to the reader for finding find the relevant proof that the author has in mind. In a similar way, tactics are instructions that we tell proof assistants (in our case Lean) to construct a proof term. __Tactics__ are like cooking recipes for making a dish while the __term proofs__ are the food. 

- The point of tactics is when we are faced with constructing a complicated proof (term), we can break down the process into multiple intermediary easier goals which we know how to solve. This is such a crucial technique not only in Lean but in all of mathematics.

- Like informal proofs, proof tactics support an incremental style of writing proofs, in which you unfold a proof and work on goals one step at a time.

- A general form of an `example` in __tactic style__: 

example (context_of_our_assumptions) : 
  statement_we_wanna_prove := 
begin
  tactic_1 [...], 
  tactic_2 [...], 
  ⋮ 
  tactic_n [...], 
end 


**Note**: Even if we prove a theorem in tactic mode, what is stored in Lean is the proof term corresponding to this tactic proof. Lean has an automatic way of converting a tactic proof to a term proof and we usually do not see this unless we use the command `show_term`. 
-/






/-! ### Tactic refl -/

-- We use `refl` instead in the _tactic mode_:
example (a b c d : ℕ) : 
(a + b) * (c + d) = (a + b) * (c + d) := 
begin 
sorry
end   


-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true

example : 
  2 + 3 = 5 
:= 
begin
  sorry 
end 

example : (0 : ℕ) + (0 : ℕ) = (0 : ℕ) := 
-- experiment with changing the first/last ℕ to ℤ 
begin
  sorry,  
end 

example (x : ℕ) : 
  x + 0 = x :=
  -- true by definition
begin
  sorry, 
end

example (x : ℕ) : 
  0 + x = x :=
  -- true by proof 
begin
  sorry
end

example : 
  (2 : ℝ) + (2 : ℝ) = (4 : ℝ) :=
begin
  sorry
end

example : (2 : ℝ) + (2 : ℕ) = (4 : ℝ) :=
begin
  -- refl,
  sorry 
end

-- try `refl` in below; does it work?
example (x y : ℝ) : x + y = y + x :=
begin
  sorry
end

-- what about here? does `refl` work?
example : ∀ x y : ℝ, (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 :=
begin
  sorry
end






/-! ### Tactic exact 
`exact` tactic allows to provide direct proof terms. If the goal is ` ⊢ X ` then `exact hp` will close the goal if and only if `hp : X`.
-/ 

-- Comment out the below lines to see various other ways that lean can display info: 
-- set_option pp.notation false
-- set_option pp.parens true

example (h : 2 + 2 = 5) : 
  2 + 2 = 5 :=
  -- The goal is to construct a proof of ` 2 + 2 = 5 `.
begin
  exact h, -- this is like copying; we copy `h` from the local context of our hypotheses
end

example (h : 2 + 2 = 5) : 
  2 + 2 = 4 :=
begin
 sorry
end

example (x : ℕ) (h : 5 = 2 + x) : 
  5 = 2 + x :=
  -- The goal is to construct a proof of ` 5 = 2 + x `.
begin
  sorry
end



end PROOFS