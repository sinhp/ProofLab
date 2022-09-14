import ..prooflab
import lectures.lec1_def_lem_thm

/-! # Homework 1: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace PROOFS 



/-! ## Question 1 (10 points): 
Use the lemma `mul_one` together with `rw` tactic to complete the proof below: 
-/

#check (mul_one : ∀ (a : ℚ), a * 1 = a)

example (x y z : ℚ) (h₁ : x * 1 = y) (h₂ : y = z)  : 
x = z := 
begin 
sorry,
end 




/-! ## Question 2 (10 points): 
Use the tactic `exact` together with the lemma `symm_of_eq`, which we proved in `lec1_def_lem_thm` to complete the following proof.  
-/

#check symm_of_eq 

example (x : ℕ) (h : x = 2) :
  2 = x := 
begin
  sorry,  
end 




/-! ## Question 3 (20 points)
Use `rw` and the lemma `mul_assoc` to prove the `example` below.
-/ 

#check ( mul_assoc : ∀ (a b c : ℝ), a * b * c = a * (b * c) )

example (a b c : ℝ) : 
  3 * a * b * c = 3 * a * (b * c) := 
begin
  sorry,
end  




/-! ## Question 4 (20 points)
Complete the next proof using the following lemma:
  `sub_self x : x - x = 0`
-/

section 
variable x : ℝ
#check sub_self x
end -- end of section

example (a b c d : ℝ) (h₁ : c = 1 + b * a - d) (h₂ : d = 1 + a * b) : 
  c = 0 :=
begin
  rw mul_comm at h₂, 
  rw h₂ at h₁, 
  sorry, 
end




/-! ## Question 5 (20 points)
Complete the next proof using lemmas `mul_assoc` and `mul_comm`:
-/

#check ( mul_assoc : ∀ (a b c : ℝ), a * b * c = a * (b * c) )
#check ( mul_comm : ∀ (a b : ℝ), a * b = b * a )

example (a b c : ℝ) : 
  (c * b) * a = b * (a * c) :=
begin
  sorry,
end




/-! ## Question 6 (20 points)
Next exercises shows that the negation flips the strict order on real numbers. Complete the next proof using lemmas `neg_neg` and `neg_lt`:
-/

section 
variables x y : ℝ
#check (neg_neg : ∀ a : ℝ, - -a = a)
#check (neg_lt.mpr : -x < y → -y < x)
#check (neg_lt : -x < y ↔ -y < x)
end  
/- 

-/
example  {x y : ℝ} (h : x < y) 
  : - y < - x := 
begin
  sorry, 
end   



end PROOFS