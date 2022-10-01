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
Prove the following statement. You might like to use any of the following lemmas (most likely you need only some of them not all.): 
- `abs_mul` 
- `abs_lt`.
- `abs_nonneg`
- `abs_pos`
- `real_le_of_mul_nonneg_left`
- `real_lt_of_mul_pos_right`
- `real_le_mul_right`
-/

section 
variables a b : ℝ
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_lt : |a| < b ↔ -b < a ∧ a < b)
end 


lemma real_le_of_mul_nonneg_left {a b c : ℝ} (h₀ : a < b) (h₁ : 0 ≤ c): 
  c * a ≤ c * b := 
begin
  apply mul_le_mul_of_nonneg_left, 
  {
    apply le_of_lt,
    apply h₀, 
  },
  {
     apply h₁, 
  },
end   


lemma real_lt_of_mul_pos_right {a b c : ℝ} (h₀ : a < b) (h₁ : 0 < c): 
  a * c < b * c := 
begin
  rw mul_comm a c,
  rw mul_comm b c, 
  apply mul_lt_mul_of_pos_left, 
  assumption',
end 


lemma real_le_mul_right {a b c : ℝ} (h₀ : a ≤ b) (h₁ : 0 < c): 
  a * c ≤ b * c := 
begin
  apply (mul_le_mul_right h₁).mpr,
  assumption,  
end 

#check abs_nonneg
 




example (x y ε : ℝ) : 
  (0 < ε ∧ ε ≤ 1) → (abs x < ε ∧ abs y < ε) → abs (x * y) < ε :=
begin
  sorry,  
end   




end PROOFS