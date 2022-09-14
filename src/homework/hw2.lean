import ..prooflab
import lectures.algebraic_identities
import lectures.function

/-! # Homework 2 
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

/-
Tactics we have learned before Homework 2:
1. `refl`
2. `exact`
3. `rw` and its variants
4. `change` 
5. `calc` 
6. `ring`
7. `linear_combination`
-/



set_option pp.beta true
set_option pp.generalized_field_notation false

namespace PROOFS 

variable {X : Type}



/-! ## Question 1 (10 points): 
Use `rw` tactic together the lemmas `mul_one` and `one_mul` to construct a proof to the statement below. You are only allowed to use `rw` tactic and no other tactic. 
-/

#check (mul_one : ∀ (a : ℚ), a * 1 = a)
#check (one_mul : ∀ (a : ℚ), 1 * a = a)

example (x y z : ℚ) (h₁ : x * 1 = 1 * y) (h₂ : y = z)  : 
  x = z := 
begin 
  sorry,
end 






/-! ## Question 2 (20 points): 
Use the tactic `calc` in conjunction with the following lemmas to prove that given rational numbers `a`, `b`, and `c`, if `b * a = 1` and `a * c = 1` then `b = c`.  
-/

#check mul_one
#check one_mul
#check mul_assoc 

example (a b c : ℚ) (h₁ : b * a = 1) (h₂ : a * c = 1) :
  b = c :=
begin
  sorry,
end 





/-! ## Question 3 (20 points)
Use `rw` and the lemmas below to comeplete the proof the `example` below.
-/ 

#check pow_two
#check mul_add 
#check add_mul 
#check add_assoc
#check add_comm
#check one_mul
#check mul_one
#check two_mul 
#check mul_two


example (a : ℝ) : 
  (a + 1)^2 = a^2 + 2 * a + 1 :=
begin
  calc (a + 1)^2 = (a + 1) * (a + 1) : by rw pow_two
  ...            = (a + 1) * a + (a + 1) * 1 : sorry 
  ...            = (a * a + 1 * a) + (a * 1 + 1 * 1) : sorry
  ...            = (a^2 + a) + (a + 1) : sorry
  ...            = a^2 + 2 * a + 1 : by sorry
end 






/-! ## Question 4 (25 points): 
Construct a proof for the following statement using any tactics we heav learned (tactics 1-7 in the list at the top of this file) except `ring` and only the lemmas we have learned so far. 
-/

example (a b : ℝ) : 
  a^4 - b^4 = (a^2 + b^2) * (a + b) * (a - b) :=
begin 
  sorry,
end 






/-! ## Question 5 (25 points): 
1. For a type `X`, Define the function `triple_shuffle` which takes a triple `(a, b, c)` as in input, where `a b c : X`, and returns the triple `(b , c, a)` 
-/

def triple_shuffle  : X × X × X → X × X × X := 
sorry 

/-
2. Evaluate the application of `triple_shuffle` to `(1,2,3)`. 
-/

/-
3. Evaluate the application of `triple_shuffle` to `triple_shuffle (1,2,3)`. 
-/


/-
4. Prove that third application of `triple_shuffle` to the triple `(1,2,3)` is equal to `(1,2,3)`. 
-/
example :  
triple_shuffle (triple_shuffle (triple_shuffle (1,2,3) )) = (1,2,3) := 
begin
  sorry, 
end 






end PROOFS