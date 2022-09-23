import ..prooflab
import lectures.lec4_equality_of_functions


/-! # Homework 3 
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions using only the tactics we have learned so far. -/


namespace PROOFS


/- 
We know that we can add any two natural numbers and get a natural number. In fact, as we have already seen we have the following function which takes __any__ two natural numbers `m` and `n` as input and returns `m + n`. 
-/

#check nat.add 


/-
Sometimes this fact is phrased as "natural numbers are closed under addition". But natural numbers are not closed under subtraction; we know that 4 subtracted from 3 is not a natural number. However, Lean has a notion of truncated subtraction which defined `m - n` to be `0` if `m < n` and if `n ≤ m`, it returns the usual nonnegative subtraction `m - n`. 
-/

#eval 4 - 3 
#eval 3 - 4



def add_one (n : ℕ) := 
n + 1 

def sub_one (n : ℕ) :=
n - 1


/-! ## Question 1 (20 points): 
Prove the following equality of functions.  
-/


example : 
  sub_one ∘ add_one = id :=
begin
  sorry, 
end 







/-! ## Question 2 (20 points): 
Fill in   
-/
  

example (f : bool → bool) (h : f ∘ f = f) : 
   f ∘ f ∘ f = f :=
begin
  sorry, 
end 







/-
### Question 3 (30 points): 
1. Compose functions `square` and `add_one` to define two functions `square_succ` and `succ_square` where the first function maps `n : ℕ` to `(n + 1) * (n + 1)` and the second function maps `n : ℕ` to `n * n + 1`. 

2. Prove that the function `square_succ` is the same as `shift_plus1 square` where `shift_plus1` is defined in below. 
-/

#check square 
#check add_one

def square_succ := sorry
#eval square_succ 20

def succ_square := sorry
#eval succ_square 20



def shift_plus1 := λ f : ℕ → ℕ, λ n, f(n + 1)
def shift_minus1 := λ f : ℕ → ℕ, λ n, f(n - 1)

example : 
  shift_plus1 square = square_succ := 
begin
  sorry, 
end 





/- ### Question 4 (30 points): 
A functions `f` is a __left inverse__ to a function `g` if `f ∘ g = id`.  
-/
@[simp] def left_inv {A B : Type} (f : A → B) (g : B → A)  := f ∘ g = id 

#check left_inv


/-
A functions `g` is a __right inverse__ to a function `f` if `f ∘ g = id`. 
-/

@[simp] def right_inv {A B : Type} (g : B → A) (f : A → B) := f ∘ g = id


/- Complete the proof of the lemma 
`inv_of_left_inv_and_right_inv` in below which says that if a function has both a left inverse and a right inverse, then they are equal. 
-/

lemma inv_of_left_inv_and_right_inv {A B : Type} (f : A → B) (g : B → A) (k : A → B) (h₁ : left_inv f g) (h₂ : right_inv k g ) : 
k = f :=
-- the statement above says that if `f` is a left inverse of `g` and `k` is a right inverse of `g` then `k = f`. 
begin
   funext, 
   calc 
   k x = (id ∘ k) x : sorry
   ... = ((f ∘ g) ∘ k) x : sorry 
   ... = f ((g ∘ k) x) : sorry 
   ... = f (id x) : sorry 
   ... = f x : by sorry, 
end  




end PROOFS