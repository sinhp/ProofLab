import ..prooflab
import lectures.lec8_structure_unbundled
import lectures.lec9_structure_bundled
import data.matrix.notation
import linear_algebra.matrix.determinant
import data.real.basic



/-! # Homework 7: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far. 
-/


-- set_option pp.all true

open PROOFS

open PROOFS.STR


#check preorder

variables {X Y Z : Type}



/-! ## Question 1: 
The following question has two parts. 
-/

/- **Part I** 
We define the structure `Q1` and `Q2` similar to `R1` and `R2` of the lecture. -/ 

@[ext] 
structure Q1 := (x : ℚ)  

@[ext] 
structure Q2 := (x : ℚ) (y : ℚ)


/-
Define the operations of addition and multiplication on `Q1` and `Q2` and prove that they are associative and commutative. 
-/

@[simp]
def Q1.add (p q : Q1) : Q1 := sorry 

@[simp]
def Q2.add (p q : Q2) : Q2 := sorry 



theorem Q2.add_comm (p q : Q2) : 
   p .add q = q .add p :=
begin
 sorry, 
end 


theorem Q2.add_assoc (p q r : Q2) : 
   (p .add q) .add r = p .add (q .add r) :=
begin
 sorry, 
end 



/- **Part II** : Given two points `p` and `q` in `Q2`, define their midpoint (https://en.wikipedia.org/wiki/Midpoint).
-/  

@[simp]
def Q2.midpoint (p q : Q2) : Q2 := sorry 





/-!
## Question 2 : 
We define the structure `bijection` in below. Show that every equivalence gives rise to a bijection by filling in `sorry` placeholders. 
-/


structure bijection (X Y : Type) :=
  (to_fun : X → Y)
  (inj : is_injective to_fun)
  (surj : is_surjective to_fun)



def bijection_of_equiv (f : fun_equiv X Y) : bijection X Y := 
{
  to_fun := f.to_fun, 
  inj :=    by { sorry, },
  surj :=   by { sorry, },
}









/-!  ## Question 3 : 
__Matrices__ in Lean are encoded as list of lists. Consider the 2x2 matrix with entries in ℝ whose first row is `[(1/2:ℚ), 0]` and whose second row is `[0, (1/2:ℚ)]`.  This matrix is encoded in Lean as follows: 
-/


#check !![(1/2 :ℚ), 0; 0, (1/2 :ℚ)]

def M₁ := !![(1/2 :ℚ), 0 ; 0, (1/2 :ℚ)]

-- #check M₁
-- #print M₁

-- The entries `M_{0,0}` (first row, first column entry), `M_{0,1}` (first row, second column entry), etc can be accessed as in below

#check M₁ 0 0 

#eval M₁ 0 0 
#eval M₁ 0 1 
#eval M₁ 1 0
#eval M₁ 1 1

/-
The usual representation of matrix M₁

       -                  -
      | M₁ 0 0  ,  M₁ 0 1  |
      |                    |
      | M₁ 1 0  ,  M₁ 1 1  |
       -                  - 

-/


-- a new matrix 
def M₂ := !![(1 : ℚ), -10; 0, 2]

-- #check M₂
-- #print M₂
-- #eval M₂ 0 0 

/-
We can add and multiply matrices: 

- addition: The sum `A + B` of two m-by-n matrices A and B is again an m-by-n matrix and is calculated entrywise:
(A + B)_{i,j} = A_{i,j} + B_{i,j}, where 0 ≤ i ≤ m - 1 and 0 ≤ j ≤ n - 1

- multiplication: if `M` is a matrix of the size 
k-by-m and  `N` is matrix of the size m-by-n then the multiplication of `M` and `N` is a matrix of size k-by-n. 
See https://en.wikipedia.org/wiki/Matrix_(mathematics)#Matrix_multiplication if you have not seen matrix multiplication before.  
-/


#eval matrix.mul M₁ M₂






/- The following is a function Q2 → Q2 which takes a vector of Q2 and mutiplies that vector by the matrix `M₁`. Note that the type `Q2` is introduced in Question 1. -/


def M₁_transform (v : Q2)  : Q2 := 
{ 
  x := (matrix.mul M₁ !![(v.x) ; (v.y)]) 0 0, 
  y := (matrix.mul M₁ !![(v.x) ; (v.y)]) 1 0,
}

section 
variables a b : ℚ
#check M₁_transform
#check M₁_transform ⟨a, b⟩
#check M₁_transform ⟨0, 1⟩
#eval M₁_transform ⟨3, -4⟩
end 


lemma M₁_mid (v : Q2) :  
  M₁_transform (v : Q2) = Q2.midpoint v v := 
begin
  sorry, 
end  




def Q2.is_additive_fun (f : Q2 → Q2) := 
∀ x y : Q2, f (x .add  y) =  (f x) .add (f y) 

/-
Prove that `M₁_transform` is an additive function. 
-/

theorem M₁_mul_additive  : 
  Q2.is_additive_fun M₁_transform := 
begin
  sorry, 
end 





/- **Questions 3 and 4 in below rely on the concept of sequences**.-/


/-
A __sequence__ in a type `X` is simply a function `a : ℕ → X`. The sequence `a` assigns to every natural number `n : ℕ` an element `a(n) : X` . In informal math texts, by convention, people write "a_{n}" for `a(n)` and "(a_{n})"" for the sequence `a : ℕ → X`. The notation "(a_{n})" communicates the idea of a sequence as an _infinite list_. Note that in lists, in contrast to sets, the order of appearance of elements matter. 

Here are some examples of sequences:
- `a : ℕ → ℤ` where `a n = (-1)^(n)`; the sequence terms are `1,-1,1,-1,...`
- `b : ℕ → ℚ` in `ℚ` where `b n = n/(1+n : ℚ)`; the sequence terms are 
`0,1/2, 2/3, 3/4,...` 
-/


/-
We can add and multiply sequences in `ℝ` component-wise, i.e. the sum `a + b` of sequences 
-/


section 
variables a b : ℕ → ℝ
variable n : ℕ 
#check a n 
#check b n 
#check a n + b n
#check (a + b) n
end 

lemma sum_of_seq_component_wise {a b : ℕ → ℝ} : 
  ∀ n : ℕ, (a + b) n = a n + b n  := 
begin
  intro n, 
  refl, 
end   




/- As we saw in the lecture on bundled structures, an structure may depend on a parameter. Here we define the structure of __upper bounds__ for sequences. Note that the structure `upper_bound` depends on a sequence `a : ℕ → ℝ`. The structure `upper_bound` consists of all sequences in `ℝ` with an explicit upper bound.
-/

structure upper_bound (a : ℕ → ℝ) :=
(ub : ℝ) -- the explicit data of upper bound 
(le_ub : ∀ (n : ℕ), a n ≤ ub) -- th property of `ub` being an upper bound: all values of the sequence `a` are less than the bound `ub`. 

section 

variables (a : ℕ → ℝ) (M : upper_bound a)
#check upper_bound
#print upper_bound

#check upper_bound a

#check @upper_bound.ub
#check @upper_bound.ub a 
#check @upper_bound.ub a M
#check M.ub
end 


/-! ## Question 3 :  
 Construct an upper bound for the sequence given by numbers `n/n+1` for `n : ℕ` by supplying correct expressions for `sorry` placeholders. The following lemmas might be useful. Also, the tactic `norm_cast` is useful when you want to prove something about a natural number treated as an integer, rational, or real number (or more generally when you have coercion). Here is a minial example of `norm_cast`. -/


example (n : ℕ) (h : 2 < n) : 
  2 < (n : ℝ) :=
begin 
  -- note that `exact h` does not work since `n` in the goal is a real numebr. 
  norm_cast, 
  exact h, 
end 

#check @div_le_iff
#check @div_le_div
#check @div_one
#check div_one (1 : ℝ)


def upbound_n_over_succ_n : 
  upper_bound (λ n, n/(1 + n : ℝ)) := 
{
  ub := sorry, 
  le_ub := by {sorry},
}






/-! ## Question 4 :  
Construct an upper bound for the sum of two upper bounded sequences by completing the (instance) definition below. You might like to use the lemma `add_le_add`. -/ 

def ub_sum_of_ub_seq (a b : ℕ → ℝ) (Ma : upper_bound a) (Mb : upper_bound b) :
upper_bound (a + b) := 
{
  ub := sorry, 
  le_ub := by {sorry},
}











