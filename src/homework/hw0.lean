import ..prooflab
import lectures.lec0_intro

/-! # Homework 0 
Homework must be done individually.
Replace the placeholders `sorry` with your proofs only using tactics `refl`, `exact` and `rw`. 
-/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace PROOFS 



/-! ## Question 1  -/

example (x y : ℕ) : 
  y + 0 = y :=
begin
  refl, 
end




/-! ## Question 2 -/

example (m n : ℕ) (h₁ : n = 4) (h₂: m^2 = n) : 
  n = m^2 := 
begin
 rw h₂,
end




/-! ## Question 3 -/

example (x y : ℕ) (h₁ : y = x) (h₂ : y - 1 = 0) : 
 5^(y - 1) = (2 + 3)^(x - 1) :=
begin
  rw h₁, 
end




/-! ## Question 4 -/

example (x y : ℕ) (h₁ : y = x) (h₂ : x - 1 = 0) : 
 5^(y - 1) = 5^0 :=
begin
  rw h₁, -- this changes `y` to `x` in the left hand side of the goal. Therefore, our new goal is 5^(x-1) = 5 ^ 0 
  rw h₂, -- this turns `x-1` into `0` by virtue of `h₂`
end




/-! ## Question 5 -/

example (a b c x y z : ℕ) (h₁ : 26 = x^2 + y^2 + z^2) 
(h₂ : x^2 = 2 * a) (h₃ : y^2 = b) (h₄ : z^2 = 2) : 
2 * a + b + 2 - z = 26 - z := 
begin
 rw ← h₂, 
 rw ← h₃, 
 rw h₁, 
 rw h₄, 
end 




end PROOFS