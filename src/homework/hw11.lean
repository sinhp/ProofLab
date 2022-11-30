/- 
Homeowork 11  
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec14_inductive_naturals
import homework.hw10


open PROOFS 
open PROOFS.STR 



/-
Note that the code below is not wrapped by the namespace `mat`, so if you want to use a definition or lemma/theorem named `xyz` from lec14 you need to append `mat` to its name and use it as `mat.xyz`. 
-/



/-! ## Question 1 (20 pts) : 
Prove the following results using `cases` or `induction`. 
-/


lemma mat.zero_of_add_eq_zero (m n : mat) : 
  m + n = 0  → (m = 0) ∧ (n = 0) := 
begin
 sorry,  
end    


lemma mat.zero_of_mul_eq_zero (m n : mat) : 
  m * n = 0  → (m = 0) ∨ (n = 0) := 
begin
  sorry, 
end 



/-! ## Question 2 (20 pts) : 
Prove the following distributivity result and then use them to prove lemma `mat.two_mul` (a proof of `mat.two_mul` which does not use distributivity lemmas is also accepted). 
-/

lemma mat.mul_add_distrib (k m n : mat) : 
  k * (m + n) = k * m + k * n := 
begin
  sorry, 
end   
#check nat.left_distrib



lemma mat.add_mul_distrib (m n s : mat) : 
  (m + n) * s = m  * s + n * s := 
begin
  sorry, 
end   


lemma mat.two_mul (m : mat) : 
  2 * m = m + m := 
begin
  sorry, 
end   






/-! ## Question 3 (20 pts) : 
In this exercise you will prove that for any natural number `n`, 
`2 * (1 + ... + n) = n * (n + 1)`
which is allegedly proved by Gauss in the 18th century when he was a primary school student. https://nrich.maths.org/2478
-/

#check mat.sum_up_to --defined in the lecture 


/- To prove this statement we need to prove an additional lemma to the repository of lemmas proved about `mat` in lecture 14.  -/


theorem sum_up_to_closed_formula : 
  ∀ n : mat, 2 * (mat.sum_up_to n) = n * (n + 1) :=
begin
  sorry, 
end   








/-! ## Question 4 (20 pts)-/

variables {X Y : Type}


def has_retract (f : X → Y) : Prop := 
∃ r : Y → X, r ∘ f = id 


lemma retract_inj {f : X → Y} : 
  has_retract f → is_injective f :=
begin
  sorry, 
end 

/-
Use the lemma `has_retract` above to prove that the function `mat.succ` is injective.
-/

#check mat.succ

lemma inj_succ : 
  is_injective mat.succ :=
begin
 sorry, 
end   







/-! ## Question 5 (20 pts)
Give a different proof that `mat.succ` is injective by filling in `sorry` placeholder below. 
-/

@[simp]
def diagonal : mat → mat → Prop
| (mat.succ m) (mat.succ n) := (m = n)
| _     _     := true



lemma succ_inj (m n : mat) (h₁ : mat.succ m = mat.succ n) : 
  m = n :=
begin
  have h₂ : (mat.succ m = mat.succ n) → diagonal (mat.succ m) (mat.succ n), sorry,  
  have h₃ : diagonal (mat.succ m) (mat.succ n), sorry,  
  have h₄ : m = n, by sorry, 
  sorry, 
end 






/-! ## Question 6 (20 pts) 
Equip `mat` with the structure of a preorder by completing the following instance where the `≤` relation is defined as in below: 
-/ 

def mat.le (m n : mat) : Prop := ∃ k, m + k = n

--#check mat.le


lemma add_cancel {k m n : mat} : 
  (k + m = k + n) → m = n := 
begin 
  intro h, 
  -- want to prove m = n, 
  induction k with d ihd, 
  {
    sorry,
  },
  {
    sorry, 
  },
  
end 


/-
Prove that ≤ relation 
-/
lemma mat.le_antisymm (m n : mat) : 
  (mat.le m n) → (mat.le n m) → m = n := 
begin
  intros h₁ h₂, 
  obtain ⟨k, hk⟩ := h₁, 
  obtain ⟨l, hl⟩ := h₂,  
  sorry,  
end 




/-! ## Question 7 (20 pts) 
Equip `mat` with the structure of a preorder by completing the following instance where the `≤` relation is defined as in below: 
-/ 

instance additive_preorder_mat : preorder mat := 
{ 
  le := mat.le, 
  lt := sorry,
  le_refl := sorry,
  le_trans := sorry,
  lt_iff_le_not_le := sorry,   
}

#reduce additive_preorder_mat.le






/-! ## Question 8 (20 pts)
We define __exponentiation__ for the type `mat`. Then you should prove that all powers of a positive number are positive. 
-/


def mat.power : mat → mat → mat
| m 0        := 1
| m (n + 1)  := (mat.power m n) * m


example : 
  mat.power 4 3 = 64 := 
begin
  refl, 
end 

postfix ` ^^ `:15  := mat.power


example : 0 ^^ 31 = 0 := 
begin
  refl, 
end  


@[simp]
lemma power_succ {a n : mat} : 
  a ^^  n.succ = (a ^^ n)  * a := 
begin
  refl, 
end   
 

-- Use induction on natural numbers to prove the following theorem. You may need to prove an extra lemma before that which states that the multiplication of two positive numbers  `a b : mat` is again positive (`a` is positive here means that `0 < a` which is inherited from the type class `preorder` and the fact that we gave an instance of preorder structure for type `mat`. ). 
theorem pos_of_power_of_pos (a : mat) : 
  ∀ n : mat, (0 < a) → (0 < (a^^n)) :=
begin
  sorry, 
end




