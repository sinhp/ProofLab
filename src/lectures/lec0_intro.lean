/- 
Introduction to Lean
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
1. `refl` 
2. `exact`
3. `rw` and its variants 
4. `change`
-/

namespace PROOFS






/-! # What is Lean 

Lean is a functional programming language (developed by Leonardo de Moura at Microsoft Research) that makes it easy to write correct and maintainable code. We use Lean as an __interactive theorem prover__. 
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
#check ℤ -- integers 
#check ℚ -- rationals 
#check ℝ -- real numbers 

#check empty 

-- All types, except the __empty__ type, have terms (or elements, or inhabitants). For instance `0 : ℕ`. We read the expression `a : A` as `a is an A`. So `0 : ℕ` says `0 is a natural number`, and `0 : ℤ` says that `0 is an integer`. 


section -- `section` declares an environment 
#check bool -- the type of booleans
#check tt 
#check ff 
-- you can put parentheses around an infix operation (like disjunction and conjunction) to talk about the operation itself.
#check (∨)
#check (∧)

#check 0
#check (0 : ℤ)
#check 2 + 2

#check (2 : ℝ)


#check ([1, 2, 3] : list ℤ)  -- bracket notation for lists 
#check [(1 : ℕ), (-1 : ℤ) ] -- gives error because the members of the list must have the same types 
#check (1, 2, 3) -- round brackets for tuples
#check ((1 : ℝ), (-1 : ℝ))
#check ((1,-1) : ℝ × ℝ)
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
variable A : Type -- "Let A be a type"
variable A' : Type
variables B C X Y Z U V W : Type
 
/- 
We do not know anything about types `A .... W` excepts that they are types. We don't even know if they have any terms. 

Note that the variables `A ... W` are global variables which means they are accessible throughout the entire file, and any file which imports this file. 
-/






/-! ### New Types from the Old -/

section 
#check A × B -- the type of pairs 
#check A ⊕ B  -- the sum type 
#check A → B -- the type of functions which we talk about in the lecture: a term of type A → B is a function which takes a term of A and returns a term of B. 
#check λ (x : ℤ), x + 1
#check λ (x : ℝ), x + 2 
#check list A
#check list empty 
#check ([] : list empty)
#check ([] : list ℕ)


#check [1,16]
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
#check 2 + 2 = 5 -- the command #check does not check the validity only the type
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
-- Terms of propositions are proofs of propositions.
#check (rfl : 1 = 1)
#check (rfl : 2 + 2 = 4) --rfl refers to "reflexivity"
#check rfl  
#check @rfl
#check ∀ x y : ℤ, x + y = y + x
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

A general __term style__ form of an `example` is as follows: 

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

- The point of tactics -- and this point becomes clear after the third lecture -- is when we are faced with constructing a complicated proof, we can break down the process into __multiple intermediary easier goals__ which we know how to solve. This is such a crucial technique not only in Lean but in all of mathematics. And while we are constructing these smaller proofs to be later composed, we interact with Lean to see the result of our instructions.

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


**Note**: Even if we prove a theorem in tactic mode, what is __stored__ in Lean is the __proof term__ corresponding to this tactic proof. Lean has an automatic way of converting a tactic proof to a term proof and we usually do not see this unless we use the command `show_term`. 
-/






/-! ### Tactic refl -/

example : 
  3 = 1 + 2 :=
begin 
  refl, -- refl is a tactic corresponding to reflexitivity proof
end   



-- We use `refl` instead in the _tactic mode_:
example (a b c d : ℕ) : 
  (a + b) * (c + d) = (a + b) * (c + d) := 
begin 
refl,
end   


-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true

example : 
  2 + 3 = 5 
:= 
begin
  refl,
end 

example : (0 : ℕ) + (0 : ℕ) = (0 : ℕ) := 
-- experiment with changing the first/last ℕ to ℤ 
begin
  refl,  
end 

example : (0 : ℤ) + (0 : ℕ) = (0 : ℤ ) := 
-- experiment with changing the first/last ℕ to ℤ 
-- this has something to do with coersion 
begin
  refl,  
end 



example (x : ℕ) : 
  x + 0 = x :=
  -- true by definition
begin
  refl, 
end

#check nat.add


example (x : ℕ) : 
  0 + x = x :=
  -- true by proof 
begin
  sorry
end

example : 
  (2 : ℝ) + (2 : ℝ) = (4 : ℝ) :=
begin
  refl,
end

example : (2 : ℝ) + (2 : ℕ) = (4 : ℝ) :=
begin
  -- refl,
  refl, -- why did previous one work?
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
 refl,
end

example (x : ℕ) (h₁ : 5 = 2 + x) (h₂ : 2 + x = 4) : 
  5 = 2 + x :=
  -- The goal is to construct a proof of ` 5 = 2 + x `.
begin
  exact h₁,
end




/-! ### Tactic rewrite 

The equality symbol `=` is meant to formalize what we mean when we say “something is the same as something else” (e.g. “ascorbic acid is vitamin C” or “5+7=12” ). We are asserting that two different descriptions refer to the same object. Since the notion of equality is very general and can be applied to virtually any domain of discourse, it is falling under the purview of logic.

One of the earliest kind of proofs one encounters in mathematics is proof by calculation. This usually involves a chaing of equalities using lemmas expressing  properties of operations on numbers and other structures. It also uses the fundamental properties of equality: 
  
  If two terms denote the same thing, then we should be able to substitute one for any other in any expression. Let's say `E` is an expression containing `a` somewhere: `E = ... a ...`. 
  If ` a = a' ` then we should be able to replace ` a ` with ` a' ` in `E` and get the same expression, that is the expression 
  `E = ... a ... = ...  a' ... `. 

  This operation is called rewriting, and the Lean "tactic" for this is `rw`.
-/


example (m n : ℕ) (h₁ : m + 1 = 7) (h₂ : n = m) : 
  n + 1 = 7 := 
begin
  -- we want to prove that `n + 1 = 7`. Since we know that `n = m` we need to replace `n` by `m` in the goal. Then we use hypothesis `h₁`. 
  rw h₂, -- replaces `n` by `m` in the goal.
  exact h₁, -- use the hypothesis `h₁` to finish the proof.
end


-- transitivity of equality via `rw`
example (x y z : ℝ) (h₁ : x = y) (h₂ : y = z) : 
  x = z := 
begin
  rw h₁, -- changes the goal `x = z` to `y = z` by replacing `x` with `y` in virtue of `h₁`. 
  -- all we need to prove now is `y = z` which we do by `h₂`.  
  exact h₂,   
end 

#check eq.trans


-- symmetry of equality via `rw`
example {X : Type} (x y : X) (h₁ : x = y) : 
  y = x := 
begin
  rw h₁, 
end 
#check eq.symm


-- try refl first; what do you get?
example (x y : ℕ) (h₁ : x = 0) (h₂ : y = 0) :
  x + y = 0 := 
begin
  -- refl, 
  rw h₁, -- Uses the hypothesis h₁ : x = 0 to change all x's to 0's in the goal.
  rw h₂, -- Uses the hypothesis h₂ : y = 0 to change all y's to 0's in the goal.
  -- 0 + 0 = 0 is done 
end 


-- try refl first, why does it not work? 
example (x y : ℕ) (h : x = y) : 
  x + 0 = y + 0 := 
begin
-- refl, 
rw h, 
end   


/-! #### Variants of rewrite-/

/- 
We already have seen the simple version of the rewrite tactic: 
1. `rw h₁` (rewrites `h₁` in the current goal)

We now see some useful variants of `rw` tactic: 
2. `rw ← h₁` (backward rewrite)
3. `rw h₁ at h₂` (rewrites hypothesis `h₁` in the hypothesis `h₂`)
4. `rw ← h₁  at h₂` (backward rewrites hypothesis `h₁` in the hypothesis `h₂`)
5. `rw h at *` (rewrites hypothesis `h` everywhere)
-/

/- Rewrite in the opposite direction-/
example (m n : ℕ) (h₁ : m + 1 = 7) (h₂ : m = n) : 
  n + 1 = 7 := 
begin
-- we want to prove that `n + 1 = 7`. Since, by `h₂` we know that `m = n` we need to replace `n` by `m` in the goal. However, for this we need to use `h₂` in the opposite direction of the above. Then we use the hypothesis `h₁`. 
  rw ← h₂,
  exact h₁,
end


-- transitivity of equality via `rw`
example (x y z : ℝ) (h₁ : x = y) (h₂ : y = z) : 
  x = z := 
begin
  rw h₁, -- changes the goal `x = z` to `y = z` by replacing `x` with `y` in virtue of `h₁`. 
  -- all we need to prove now is `y = z` which we do by `h₂`.  
  exact h₂,   
end 


/- another proof involves replacing `y` with `z` (in virtue of `h₂`) in hypothesis `h₁` to get a new hypothesis `x = z` which is our goal.  

This proof uses the following variant of the rewrite tactic: 
`rw h₁ at h₂` (rewrites hypothesis `h₁` in the hypothesis `h₂`)
-/

example (x y z : ℝ) (h₁ : x = y) (h₂ : y = z) : 
  x = z := 
begin
rw h₂ at h₁, 
exact h₁,
end 

#check eq.trans -- for transitivity of equality relation 



example (x : ℕ) (h₁ : 5 = 2 + x) (h₂ : 2 + x = 4) : 
  5 = 4 :=
  -- we sub 2 + x in h₁ with 4 because of h₂. 
begin 
 rw h₂ at h₁, 
 exact h₁, 
end 


/-
`rw h at *` rewrites `h` everywhere, in the goal and all hypotheses.
-/

example (x y z : ℕ) (h₁ : x = 2) (h₂ : 2 + x = y) (h₃ : z = x + 2): 
  x + z = x + y := 
begin
  rw h₃, -- this changes the goal by replacing `z` with `x + 2`
  rw ← h₂,
  rw h₁,
end      






/-! ### Tactic change -/

/- If we tweak our assumptions a little bit as follows, we are not able to directly use `rw` anymore.  -/
example (x y z : ℕ)
  (h₁ : x + 0 = y) (h₂ : y = z) : x = z :=
begin
--  rw h₁, -- fails because rw works up to syntactic equality
  change x = y at h₁, -- change works up to _definitional_ equality
  rw h₁, -- now it works
  exact h₂, 
end




end PROOFS