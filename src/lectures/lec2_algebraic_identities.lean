/- 
Algebraic identities
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/
import ..prooflab
-- import lectures.lec1_def_lem_thm

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true

/-
In this lesson, we learn new tactics which help us to prove some basic algebraic identities and polynomial arithmetic (such as difference of squares, difference of cubes, binomial identities): 

The tactics we learned so far: 
1. `refl`
2. `exact`
3. `rw` and its variants
4. `change`

The new tactics we learn 
5. `calc` 
6. `ring`
7. `linear_combination`
-/

namespace PROOFS


/-! ### Tactic calc 
- `calc` (short for calculation) should be terminated with a comma. We put the comma only after the last tactic.  See the comma after the last `sorry` in the example below. 
- Using `calc`, in order to prove our goal (`x + 1 = w + 1`) we introduce several __subgoals__ each of which needs a separate proof. The subgoals in the example below are 
1. `x + 1 = y + 1` this is true since `x = y` by virtue of `h₁`. 
2. `y + 1 = z + 2` this is true since `y + 1 = z + 2` by virtue of `h₂`
3. `z = w ` this is true since `x = y` by virtue of `h₁`

Then the tactic `calc` takes advanatge of the transitivity of equality to bind all these proofs togehter and prove that `x + 1 = w + 2`. 
-/


example (x y z w : ℝ) (h₁ : x = y) (h₂ : y + 1 = z + 2) (h₃ : z = w) : x + 1 = w + 2 :=
begin
rw ← h₃,  -- there is `w` in the goal and we want to replace it by `z` because we know `h₂` says something `z`.
rw h₁, -- we replace `x` in the goal by `y`. 
exact h₂, -- proof from the context.
end 


example (x y z w : ℝ) (h₁ : x = y) (h₂ : y + 1 = z + 2) (h₃ : z = w) : x + 1 = w + 2 :=
begin 
  calc x + 1 = y + 1 : by rw h₁ -- `x + 1 = y + 1` is the first subgoal. `by` converts tactics to terms which we need to supply as the justification for the subgoal. 
  ...    = z + 2 : by exact h₂ -- the second subgoal is that `y + 1 = z + 2` 
  ...    = w + 2 : by rw h₃, -- the third subgoal is that `z + 2 = w + 2` 
end






/-
After fixing our subgoals, in the second stage, we provide the proofs of each subgoal by replacing `sorry` with a valid proof. 
-/

example (x y z w : ℝ) (h₁ : x = y) (h₂ : y + 1 = z + 2) (h₃ : z = w) : x + 1 = w + 2 :=
begin 
  calc x + 1 = y + 1 : by rw h₁
  ...        = z + 2 : by rw h₂
  ...        = w + 2 : by rw h₃, 
end


example (x y z w : ℝ) (h₁ : x = y) (h₂ : y + 1 = z + 2) (h₃ : z = w) : x + 1 = w + 2 :=
begin 
  calc x + 1 = y + 1 : sorry 
  ...        = z + 2 : sorry 
  ...        = w + 2 : sorry, -- this is where the `calc` tactic ends so we need a comma. 
end





/-! #### Getting effective __feedback__ while using `calc`: 
To get helpful error messages, keep the calc structure even before the proof is complete. First use `sorry` (or `_`) as in above, then replace each `sorry` (or `_`) with a valid proof. Note that `sorry` will supress error messages entirely. 

If the structure of calc is incorrect (e.g., missing `:` or the justification after it), you may see error messages that are obscure and/or red squiggles that end up under a random .... To avoid these, you might first populate a skeleton proof. 
-/ 


/- 
In the example below we use the lemmas  `mul_comm` and `two_mul` (proved in mathlib/src/algebra/group/defs.lean). 
-/


section 
variables a b : ℝ
#check (mul_comm : ∀ (a b : ℝ), a * b = b * a)
#check (two_mul : ∀ (a: ℝ),  2 * a = a + a)

#check mul_two

#check (mul_comm a b : a * b = b * a)
#check (two_mul a : 2 * a = a + a)
end 

-- CHALLENGE: provide comments for each line 
example (a b c d : ℝ) (h₁ : c = d * a + b) (h₂ : b = a * d) : c = 2 * a * d :=
begin
  calc c = d * a + b   : h₁ -- or `by exact h₁`
  ... = d * a + a * d  : by rw h₂ 
  ... = a * d + a * d  : by rw mul_comm
  ... = 2 * (a * d)    : by rw ← two_mul (a * d)
  ... = 2 * a * d      : by rw ← mul_assoc,
end

-- Warning: Be careful to put exactly _three_ dots (...); otherwise you get an incomprehensile error. 







/-
Use the following lemmas to prove the so-called "difference of two squares" identity, i.e. for any two numbers (say reals), the difference of squares `x^2 - y^2` is the same as the product `(x + y) (x - y)`. Think about what this says geometrically. 
-/ 

section 
variables a b c x : ℝ
#check (pow_two x : x^2 = x * x)

#check (mul_sub a b c : a * (b - c) = a * b - a * c)
#check (add_mul a b c : (a + b) * c = a * c + b * c)

#check (add_sub a b c : a + (b - c) = (a + b) - c)
#check (sub_add a b c : a - b + c = a - (b - c))
#check (sub_sub a b c : a - b - c = a - (b + c))


#check (add_zero a : a + 0 = a)
#check (sub_self a : a - a = 0)
#check (sub_zero a : a - 0 = a)
end 



-- Difference of two squares
lemma diff_of_squares (a b : ℝ) : 
  (a + b) * (a - b) = a^2 - b^2 :=
begin
  calc   (a + b) * (a - b) = (a + b) * a - (a + b) * b : mul_sub (a + b) a b 
  ... =  (a * a + b * a) - (a * b + b * b)       : by rw [add_mul a b a, add_mul a b b]  
  ... =  (a^2 + b * a) - (a * b + b^2)            : by rw [pow_two a, pow_two b]
  ... =  a^2 + b * a - a * b - b^2                : by rw [sub_sub _ _ _ ] 
  ... =  a^2 + (b * a - a * b) - b^2              : by rw [add_sub _ _ _]
  ... =  a^2 - b^2                                : by rw [mul_comm b a, sub_self,add_zero],
end







/-!  A __system of linear equations__ problem can be solved using the tactic `calc`: 
Let `a` and `b` be integers and suppose that `a - 5 * b = 4` and `b + 2 = 3`. Show that `a = 9`.
-/
example (a b : ℤ) (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : 
  a = 9 :=
begin
  calc a = (a - 5 * b) + 5 * b : by rw [sub_add, sub_self, sub_zero]
  ...    = 4 + 5 * b : by rw [h₁]
  ...    = -6 + 5 * (b + 2) : by ring
  ...    = -6 + 5 * 3 : by rw [h₂]
  ...    = 9 : rfl,
end 







/-! ### Tactic linear_combination
We have a special tactic for the system of linear equations called `linear_combination`. Note that from the type-theoretic perspective it is nonsense to add and multiply proofs (what `h₁` and `h₂` are), but since, in the example below, we are in the tactic mode, that does not cause problems. 
-/

section 
variables (a b : ℤ) 
variables (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3)
#check h₁ + 5 * h₂ -- it is nonsense to add and multiply proofs (what `h₁` and `h₂` are), since there are no operations of addition (`+`) and multiplication (`*`) defined for propositions. 
end 

example (a b : ℤ) (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : 
  a = 9 :=
begin
linear_combination h₁ + 5 * h₂,  
end 








/-! ### Tactic ring 
Tactic for solving equations in the language of commutative (semi)rings, that is whenever we have two binary operations `+` and `*` which furthermore satisfy the followin axioms:
-/

section 
-- Associativity of addition: 
#check add_assoc 

-- Associativity of multiplication: 
#check mul_assoc

-- Commutativity of addition 
#check add_comm 

-- Commutativity of multiplication 
#check mul_comm

-- Distributivity of multiplication over addition:
#check mul_add 
#check add_mul 

-- Zero for addition 
#check add_zero 

-- One for multiplication 
#check mul_one
#check one_mul 

-- Inverse for addition 
#check sub_self 
end 



-- Difference of two squares
example (a b : ℝ) : 
  (a + b) * (a - b) = a^2 - b^2 :=
begin
  ring,
end

lemma binomial₂ (a b : ℝ) : (a + b)^2 = a^2 + 2 * (a * b) + b^2 :=
begin
  ring,
end 

lemma binomial₃ (a b : ℝ) : 
  (a + b)^3 = a^3 + 3 * a^2 * b + 3 * a * b^2 + b^3 :=
begin
  ring,
end 

lemma sum_of_cubes (a b : ℝ) :
  a^3 + b^3 = (a + b)^3 - 3 * a * b * (a + b) :=
begin
  ring, 
end 

lemma sum_cubes_fac (a b : ℝ) :
a^3 + b^3 = (a + b) * (a^2 - a * b + b^2) := 
begin
  ring,  
end 

lemma diff_of_cube (a b : ℝ) : 
  a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := 
begin
  ring,  
end   
  




/-!
`calc` can be used with a mix of equality and _inequality_ subgoal statements. Here is an example. 
-/

section 
variables a b c d : ℝ
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (lt_add_one a : a < a + 1)
#check le_of_eq
#check le_of_eq (refl a)
end 

example (a b c d : ℝ)
  (h₁ : a = b) (h₂ : b^2 ≤ c) (h₃ : c + 1 < d) : a^2 < d :=
begin 
  calc a^2 = b^2     : by rw h₁
    ...    < b^2 + 1 : lt_add_one (b ^ 2)
    ...    ≤ c + 1 : add_le_add h₂ (le_of_eq (refl 1))
    ...    < d     : h₃,
end 

end PROOFS