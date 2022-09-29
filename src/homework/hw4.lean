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

You need to use the lemma `mul_eq_one_of_pos_of_pos` in below which says if the multiplication of two positive integers is `1` then both of them must be `1`. Notice that we did not provide the proof of this lemma here, and __you don't need to provide it either__. We will construct a proof of this lemma in the next lecture. 
-/

-- no need to solve the following, just use it in the next proof 
lemma mul_eq_one_of_pos_of_pos  (m n : ℤ) (h : m * n = 1) : 
  (0 < m ∧ 0 < n) → (m = 1 ∧ n = 1) := 
begin 
  sorry, 
end 

-- give a proof of this one using the lemma above. 
example (m n : ℤ) : 
  m * n - m - n + 1 = 1 → (1 < m ∧ 1 < n) → (m = 2) ∧ (n = 2) := 
begin
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