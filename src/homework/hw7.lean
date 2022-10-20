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



variables {X Y Z : Type}



/-! ## Question 1 (20 pts): 
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
## Question 2 (20 pts) : 
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









/-!  ## Question 3 (30 pts): 
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





/- **Questions 4 and 5 in below rely on the concept of sequences**.-/


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


/-! ## Question 4 (20 pts):  
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







/-! ## Question 5 (20 pts) :  
Construct an upper bound for the sum of two upper bounded sequences by completing the (instance) definition below. You might like to use the lemma `add_le_add`. -/ 

def ub_sum_of_ub_seq (a b : ℕ → ℝ) (Ma : upper_bound a) (Mb : upper_bound b) :
upper_bound (a + b) := 
{
  ub := sorry, 
  le_ub := by {sorry},
}








/-! ## Question 6 (40 pts)
In geometry, a simplex (plural: simplexes or simplices) is a generalization of the notion of a triangle or tetrahedron to arbitrary dimensions. 

https://en.wikipedia.org/wiki/Simplex

https://en.wikipedia.org/wiki/Simplex#/media/File:2D-simplex.svg

We define the __standard geometric one-dimensional and two-dimensional simplices__ as the following structures. 


-/

@[ext]
structure standard_one_simplex :=
(x : ℝ)
(y : ℝ)
(x_nonneg : 0 ≤ x)
(y_nonneg : 0 ≤ y)
(sum_eq   : x + y = 1)


@[ext]
structure standard_two_simplex :=
(x : ℝ)
(y : ℝ)
(z : ℝ)
(x_nonneg : 0 ≤ x)
(y_nonneg : 0 ≤ y)
(z_nonneg : 0 ≤ z)
(sum_eq   : (x + y) + z = 1)

#check standard_two_simplex


/- 
We introduce the following _notations_ for the `standard_one_simplex` and `standard_two_simplex`
 -/

notation `Δ_1` := standard_one_simplex
notation `Δ_2` := standard_two_simplex



/- **Part I** : 
Construct three distinct points (i.e. instances) of `Δ_1`  and two points (i.e. instances) of `Δ_2` with the given constraints. 
-/



def Δ_1.point1 : Δ_1 := 
{
  x := 1,
  y := sorry,
  x_nonneg := by {sorry}, 
  y_nonneg := by {sorry}, 
  sum_eq := by {sorry}, 
}


def Δ_1.point2 : Δ_1 := 
{
  x := sorry,
  y := 1,
  x_nonneg := by {sorry}, 
  y_nonneg := by {sorry}, 
  sum_eq := by {sorry}, 
}


noncomputable
def Δ_1.point3 : Δ_1 := 
{
  x := 1/(2 : ℚ),
  y := sorry,
  x_nonneg := by {sorry}, 
  y_nonneg := by {sorry}, 
  sum_eq := by {sorry}, 
}




def Δ_2.point1 : Δ_2 := 
{
  x := 1,
  y := 0,
  z:= sorry,
  x_nonneg := by {sorry}, 
  y_nonneg := by {sorry},
  z_nonneg := by {sorry},
  sum_eq := by {sorry}, 
}



noncomputable
def Δ_2.point2 : Δ_2 := 
{
  x := sorry,
  y := sorry,
  z:= 1/(2 : ℚ),
  x_nonneg := by {sorry}, 
  y_nonneg := by {sorry}, 
  z_nonneg := by {sorry},
  sum_eq := by {sorry}, 
}








----------------------------------------
-- **Maps of standard n-simplices**
----------------------------------------

/-
Maps of standard simplices are induced from functions of affine plane (i.e. point3d, point2d, and point1d) with the extra constraints that they map the points in one simplex into the points of the other. The constraints become part of the data of the map between simplices. 
-/


/-
 There are two __degeneracy maps__ from the standard 2-simplex to the standard 1-simplex: try to understand the geometric idea begind these maps.
-/

/- 
**Part II** : Fill in `sorry` placeholders in below so that `dg_2d_to_1d_fst` and `dg_2d_to_1d_snd` are functions from the type `Δ_2` to `Δ_1`. 
-/

def dg_2d_to_1d_fst  (a : Δ_2) : Δ_1 
:= 
{ x := a.x, 
  y := a.y + a.z, 
  x_nonneg := by {sorry}, 
  y_nonneg := by {sorry},
  sum_eq := by {sorry}, 
}



def dg_2d_to_1d_snd  (a : Δ_2) : Δ_1
:= 
{ x := a.x + a.y, 
  y := a.z, 
  x_nonneg := by {sorry}, 
  y_nonneg := by {sorry}, 
  sum_eq := by {sorry},
}



/- **Part III**: 
Prove the following equality of points in `Δ_1`  (i.e. instance of structure `Δ_1`.) -/

example : 
  dg_2d_to_1d_fst Δ_2.point1 = Δ_1.point1 := 
begin
   sorry,
end 


example : 
  dg_2d_to_1d_snd Δ_2.point2 = Δ_1.point3 := 
begin
   sorry, 
end 













/-! ## Question 7 (30 pts) 
A __metric space__ is an abstraction of the notion of a collection of points with a way of measuring a __distance__ between each pair.
-/


/- metric space -/ 
structure metric_space (X : Type) :=
  (dist : X → X → ℝ)
  (dist_eq_zero : ∀ x y, dist x y = 0 ↔ x = y)
  (dist_symm : ∀ x y, dist x y = dist y x)
  (triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)



lemma nonneg_of_double_nonneg {a : ℝ} (h : 0 ≤ a + a) : 
  0 ≤ a := 
begin
  linarith,
end   


/- Prove that the distance between any two points in a metric space is nonnegative. You may use the lemma above. -/
lemma dist_nonneg {X : Type} (μ : metric_space X) : 
  ∀ x y : X,  0 ≤ μ.dist x y :=
begin
  sorry, 
end 






