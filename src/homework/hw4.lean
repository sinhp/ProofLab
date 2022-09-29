import ..prooflab
import lectures.lec6_proposition
import data.real.basic
import data.complex.exponential


/-! # Homework 4: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far. 

Pro Tip: Don't forget you know the tactics `linarith` and `ring`! 
 -/





namespace PROOFS


variables {P Q R : Prop}



/-! ## Question 1 (20 points): 
Give a proof of the proposition `(P ∧ R) → (R → P → Q) → Q`. 
-/

example : 
  (P ∧ R) → (R → P → Q) → Q :=
begin
  sorry, 
end 






/-! ## Question 2 (20 points): 
Prove the implication 
`m * n - m - n + 1 = 1 → (m = 2) ∧ (n = 2)` 
for natural numbers `m` and `n` by filling in `sorry` placeholders below. 

You might like to use the lemma `nat.mul_eq_one_iff.mp` which says if the multiplication of two natural numbers is `1` then both of them must be `1`
-/

section
variables m n : ℕ
#check (nat.mul_eq_one_iff.mp : m * n = 1 → m = 1 ∧ n = 1 )
end 


example (m n : ℕ) : 
  m * n - m - n + 1 = 1 → (m = 2) ∧ (n = 2) := 
begin
  intro h₁, 
  have h₂ : (m - 1) * (n - 1) = 1, sorry, 
  sorry, 
end  

 




/-! ## Question 3 (20 points): 
Construct a proof of the proposition `abs (2 * x - 1) < 5 → -2 < x `. You are allowed to use the lemma `abs_lt`.  
-/

section 
variables a b : ℝ 
#check (abs_lt : |a| < b ↔ -b < a ∧ a < b)

end 
example (x y : ℝ) : abs (2 * x - 1) < 5 → -2 < x := 
begin
  sorry, 
end



/-! ## Question 4 (20 points): 
For `x : ℝ`, the term `real.exp x` encodes the exponential e^x. 
-/

section 
variables a b c : ℝ
#check (real.exp_le_exp.mpr : a ≤ b → real.exp a ≤ real.exp b)
end 


example (a b c : ℝ) (h : 1 ≤ a ∧ b ≤ c) :
  2 + a + real.exp b ≤ 3 * a + real.exp c :=
begin
  sorry, 
end 






/-! ## Question 5 (20 points): 
Prove the following statement. You might like to use  lemmas `abs_mul` and/or `abs_lt`.
-/

section 
variables a b : ℝ
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_lt : |a| < b ↔ -b < a ∧ a < b)
end 


example (x y ε : ℝ) : 
  (0 < ε ∧ ε ≤ 1) → (abs x < ε ∧ abs y < ε) → abs (x * y) < ε :=
begin
  sorry,  
end   




end PROOFS