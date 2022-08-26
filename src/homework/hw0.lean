import ..prooflab
import lectures.lec0_intro

/-! # Homework 1 
Homework must be done individually.
Replace the placeholders `sorry` with your proofs. 
-/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace PROOFS 



/-! ## Question 1  -/

example (x y : ℕ) : 
  y + 0 = y :=
begin
  sorry,
end




/-! ## Question 2 -/

example (m n : ℕ) (h₁ : n = 4) (h₂: m^2 = n) : 
  n = m^2 := 
begin
 sorry, 
end




/-! ## Question 3 -/

example (x y : ℕ) (h₁ : y = x) (h₂ : y - 1 = 0) : 
 5^(y - 1) = (2 + 3)^(x - 1) :=
  -- The goal is to construct a proof of `5 = 2 + x`.
begin
  sorry,  
end




/-! ## Question 4 -/

example (a b c x y z : ℕ) (h₁ : x^2 + y^2 + z^2 = 26) 
(h₂ : x^2 = 2 * a) (h₃ : y^2 = b) (h₄ : z^2 = 1) : 
2 * a + b + 1 - z = 26 - z := 
begin
  sorry,  
end 



end PROOFS