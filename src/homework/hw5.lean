import ..prooflab
import lectures.lec6_proposition


/-! # Homework 5: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far. 
 -/


namespace PROOFS

/-! ## Question 1 (20 points): 
(**Part I**) Give a proof of the following propositional formula. 
-/


theorem  disj_conj {P Q R : Prop} : 
  (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) :=
begin
  sorry,
end 

/-
(**Part II**) In `lec6_proposition` we proved that 
`P ∨ Q → ¬ P → Q`. The proof was `resolve_right`. 

Use the previous theorem (`disj_conj`) to give a new proof of `P ∨ Q → ¬ P → Q`. 
-/

theorem resolve_right_alt {P Q : Prop} : 
 P ∨ Q → ¬ P → Q :=
begin
  sorry,  
end 





/-! ## Question 2 (20 points): 
Give a proof of the following statement. 
-/
example (a b c : ℝ) (h₁ : c * a ≤ c * b) (h₂ : ¬ b ≤ a) : 
  c * a ≤ c * b ∧ a ≠ b :=
begin
  sorry, 
end






/-! ## Question 3 (20 points): 
Give a proof of the following statements using only lemmas `neg_neg`, `neg_lt`, `neg_le`. The first one states that negation flips the strict order (<) , and the second one states that negation flips the order (≤).
-/

lemma lt_rev_of_neg {x y : ℝ} (h : x < y) 
  : - y < - x := 
begin
  sorry,  
end   



lemma le_rev_of_neg {x y : ℝ} (h : x ≤ y) 
  : - y ≤ - x := 
begin
  sorry, 
end 






/-! ## Question 4 (20 points): 
Use the two lemmas `lt_rev_of_neg` and `le_rev_of_neg` above together with some/all of the following lemmas to prove the following statement. 
-/

#check le_or_gt
#check abs_of_nonneg
#check abs_of_neg 
#check neg_neg
#check lt_of_lt_of_le
#check lt_of_le_of_lt
#check le_trans
#check lt_trans


example (x y : ℝ ) : 
  abs x < y ↔ - y < x ∧ x < y :=
begin
  sorry, 
end






/-! ## Question 5 (20 points): -/


def EM (P : Prop) := 
P ∨ ¬ P

#check EM 

def DN (P : Prop) :=
(¬ P → false) → P 

#check DN 



theorem excluded_implies_double_negation  {P : Prop} : EM P → DN P := 
begin 
 unfold EM, 
 unfold DN, 
 sorry, 
end 




end PROOFS