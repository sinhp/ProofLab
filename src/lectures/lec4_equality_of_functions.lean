/-
Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------

# Algebra of Functions: Part II
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec3_function

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true


/- 
New tactic we'll learn in this lesson: 
8. funext 
9. linarith
-/


namespace PROOFS

variables {A B C X Y Z U V W : Type} -- curly brackets make type implicit and that is what you get things like M_1? ... 


/-! ### Functions evaluation


**Question**: What did all the functions we defined in the previous lecture have in common? 


**Answer** : They all had one input and one output. 
-/

#check rational_sum_of_squares -- one input one output

/-
We can __evaluate__ a function at an input by applying the function to it. 
-/

#check double 
#eval double 7
#check double_alt -- the domain of this function is natural numbers and the codomain of this function is natural numbers. 
#reduce double_alt -- this function takes one input and returns one output, but it uses in its definition the function `nat.add` which takes 2 inputs and 1 output. 
#check nat.add

-- #eval double_alt 7


/- 
__The output of a function can be a function__: A function `f : A → B → C` should be read as a function `f : A → (B → C)` where for any input `a : A`, the output is a function `f a : B → C` which upon receiving an input `b : B` returns the ouput `f a b : C`. 

Given this, there are two things we should be careful about: 
1. Functions can be
* __fully applied__ (e.g., `f a b` if `f` is binary);
* __partially applied__ (e.g., `f a`);
* __left unapplied__ (e.g., `f`).

2. Evaluation/application is __left-associative__: `f a b` = `((f a) b)`.
-/


#check nat.add -- the type of `nat.add` is `ℕ → ℕ → ℕ` which is implicitly understood by Lean to be `ℕ → (ℕ → ℕ)` 
#check nat.add 1
#check nat.add 1 2
#eval nat.add 1 2
#eval nat.add 1 (2) 



def mul_square (m n : ℕ) := 
m * m * n * n

#check mul_square 
#check mul_square 1 -- the type of `mul_square 1` is `ℕ → ℕ`

/-Question: what does the function `mul_square 1` do?  -/

/- The following functions from mathlib all take 2 inputs and return 1 output -/
#check nat.add  
#check nat.mul
#check nat.le -- is a function which takes two natural number and returns a proposition. `nat.le m n` is the proposition that `m ≤ n`. `le` is short for less than or equal to. 
#check int.add
#check int.mul
#check rat.add
#check rat.mul

def sum_squares (m n : ℕ) := 
m * m + n * n

#check sum_squares
-- #check sum_squares 1 
#check sum_squares 1 2
#eval sum_squares 1 2



def fst_fun (x : X) := 
λ (y : Y), x -- the input is of type `X` and the output is a function. the domain is `X` and the codomain `Y → X`. 

-- What is the type of fst_fun? And what does it do?
#check fst_fun 
#check @fst_fun -- for all types `X` and `Y` the type of `fst_fun` is `X → Y → X`. 


def fst_fun_alt (x : X) (y : Y) := 
x 
-- What is the type of fst_fun_alt? And what does it do?
#check fst_fun_alt
#check @fst_fun_alt -- make it explicit 

#check fst_fun_alt 17 4
#eval fst_fun_alt 17 4

#check fst_fun_alt 17
#check @fst_fun 17 -- why can we not make the second variable explicit? we'll come back to this in the next lecture. 

-- CHALLENGE: define the second projection
def snd_fun  : X → Y → Y := 
λ x, λ y, y  
-- the domain of `fst_fun` and `snd_fun` are the same but not their codomain. 

-- #check snd_fun
section 
variables (x : X) (y : Y)
#check snd_fun x y
-- #eval snd_fun x y
end 


def fst (p : X × Y) := 
p.1 
-- for a pair `p`, i.e. a term of type `X × Y` the output of `fst` is the first coordinate of `p` which we access using projection `.1`. 

-- #check fst
-- #check fst
-- #check fst (1 , 2)
#check fst (2, 1)
#eval fst (2, 1)




def snd (p : X × Y) := 
p.2


/-! ### Examples of a function which take a function as its argument -/

def evaluation (f : X → Y) (x : X) := f x
#check evaluation  
#eval evaluation double 3 

-- CHALLENGE: Write `evaluation` in the lambda notation. 



-- `pairing` is a function which takes as input two functions. 
def pairing (f : Z → X) (g : Z → Y) (z : Z) : X × Y := 
(f z , g z) 


section 
variable f : Z → X 
variable g : Z → Y
#check pairing f g
end 


def pairing_alt (f : Z → X) (g : Z → Y)  := 
λ z, (f z , g z) -- abstracting over z 



section 
variables (f : Z → X) (g : Z → Y) 
#check λ z, (f z , g z)
end 


/-
Question: What does the function `pairing switch nat_of_bool` do? 
-/
#check pairing switch nat_of_bool
#eval pairing switch nat_of_bool ff
#eval pairing switch nat_of_bool tt

/-
Question: What does the function `pairing double bool_of_nat` do? 
-/
-- #check pairing double bool_of_nat



/-
Question: What does the function `cartesian_prod` do? 
-/
def cartesian_prod (f : A → B) (g : X → Y) : A × X → B × Y :=   
λ p, (f p.1, g p.2) 





def decouple (f : Z → X × Y) : (Z → X) × (Z → Y) := 
(λ z, (f z).1, λ z, (f z).2)

/-
Question: What does the function `decouple` do? 
-/

-- #check decouple (pairing switch nat_of_bool)
-- #check decouple (pairing switch nat_of_bool)


def swap (x : X) (y : Y) := 
(y , x)

/-
Question: What does the function `swap` do? 
-/

-- #check swap 

section 
-- #check swap 2 4
-- #eval swap 2 4
end 


def swap_pair (X Y : Type) : X × Y → Y × X := 
λ a, (a.2, a.1)

/-
Question: What does the function `swap_pair` do? 
-/

#check swap_pair
--#check swap_pair (7,3)
--#eval swap_pair (7,3)

def swap_pair_alt {X Y : Type} : X × Y → Y × X := 
λ a, (a.2, a.1)


example : 
  swap_pair_alt ( swap_pair_alt (1, 3) ) = (1,3)  := 
begin 
  refl, 
end 




def copy (x : X) : X × X := 
(x, x) 

#check copy
#check @copy 







def curry : (X × Y → Z) → (X → (Y → Z)) :=
 λf, λ x, λ y, f (x, y)

#check curry
#check @curry
#check @curry X Y Z

def uncurry : (X → (Y → Z)) → (X × Y → Z) := 
λ f, λ p, f p.1 p.2 
#check @uncurry
#check @uncurry X Y Z


#check curry ∘ uncurry 
#check @curry X Y Z ∘ @uncurry X Y Z

example : 
  @curry X Y Z  ∘ @uncurry X Y Z = id := 
begin
  funext f x y, 
  dsimp,
  unfold uncurry,
  unfold curry,
end 



example : 
  @uncurry X Y Z  ∘ @curry X Y Z = id := 
begin
  sorry, 
end 

--#check curry fst 
--#check (curry fst) ff 2
--#eval (curry fst) ff 2
-- #check uncurry (curry fst) (ff, 2) -- why?








/- We use `uncurry` to define the product projections from `fst_fun` and `snd_fun`. -/

#check fst_fun 
#check uncurry 

-- Challenge: Fix the following definition 
def fst_alt (f) := 
uncurry (fst_fun f)

#check fst_alt




/-
Question: What does the function `my_complicated_function` do? 
-/
def my_complicated_function : (X → Y → Z) → ((Y → X) → Y) → X → Z :=
λ f g x, f x (g (λy, x))






/-! ### Equality of Functions 
Once we have defined functions (or anything) in Lean we can prove properties of them: For instance we might want to prove two functions are equal to each other.

__Function Extensionality__ is a logical principle which says that we can prove two functions `f : X → Y` and `g : X → Y`  (with the same domain and the same codomain) are equal (written as `f = g` ) if for all elements `x : X` we have a proof of `f x = g x`. In Lean, this is `funext`. Here's a little secret: `funext` is assumed in Lean so we do not need to be explicit about it when we use it. 
-/


example : (λ n : ℕ, (2 * n)) = (λ n: ℕ, n + n) := 
begin
 funext x, -- we fix x : ℕ (alternatively, let n: ℕ be given)
 rw two_mul, -- we need to prove 2 * n = n + n which is proved by lemma `two_mul`
end 



example : (λ n : ℕ, (2 * n)) = (λ n: ℕ, n + n) := 
begin
 funext x, -- we fix x : ℕ (alternatively, let n: ℕ be given)
 rw ← two_mul, 
 -- we need to prove 2 * n = n + n which is proved by lemma `two_mul`
end 



example : (λ n : ℕ, (2 * n)) = (λ n: ℕ, n + n) := 
begin
 funext, -- we fix n : ℕ (alternatively, let n: ℕ be given)
 exact two_mul n,
end 









example : (λ n : ℕ, (2 * n)) = (λ n: ℕ, n + n) := 
begin
funext, 
-- After ext, we must show that given x : ℕ, we have 2 * x = x + x
-- refl, note that refl does not work. what error do you get if you try refl after ext? 
ring,
end 




example : (λ n : ℕ, (2 * n)) = (λ n: ℕ, n + n) := 
begin
funext, 
-- After ext, we must show that given x : ℕ, we have 2 * x = x + x
-- refl, note that refl does not work. what error do you get if you try refl after ext? 
ring,
end 



example : 
  mul_square 1 = square := 
begin 
  ext a, 
  rw mul_square,
  rw square, 
  ring, 
end  



#check two_mul

example : double = double_alt := 
begin 
funext x,
rw double, 
rw double_alt, 
exact two_mul x, 
end 



example : double = double_alt := 
begin 
-- ext n, -- instead of the default variable name x : ℕ , we use n : ℕ. 
ext n,
rw double,
rw double_alt, 
linarith,  -- we cannot use `ring` here, since natural numbers do not form a ring (recall that a ring). `linarith` is for linear arithmetic.   
end 



lemma fun_cong_two_args (a a' b b' : X)
    (f : X → X → X) (ha : a = a') (hb : b = b') :
  f a b = f a' b' :=
begin
  rw ha,
  rw hb,
end






/-! ### Functions out of empty type 
There is a type which is called the __empty__ type and is denoted by `empty` in Lean. This type does not have any terms in it. Therefore, to specify a function with domain `empty` and codomain `X` (for any type `X`) we do not need to do anything, since there is no term in `empty` for which we need to return a term of `X`. Therefore, there is always a function `empty → X` for any type `X`. 
-/

#check empty.elim
#check (empty.elim : empty → X)


/- Let's prove that any two functions of type `empty → X` are equal. Therefore, there is a __unique__ function `empty → X`. -/

lemma empty_unique_fun (f g : empty → X) : 
  f = g :=
begin
  funext, 
  exact empty.elim x, 
end  



/-! ### Functions out of unit type 
There is a type which is called the __unit__ type and is denoted by `unit` in Lean. This type has exactly one term in it which is `unit.star`.
-/


#check unit
#print unit
#check unit.star




/- To specify a function with domain `unit` and codomain `X` (for any type `X`) we need to specify which term of `X` is assigned to `unit.star`, in other words which term of `X` does this function return for the input `unit.star`. Therefore there are as many functions `unit → X` as the terms/elements of `X`-/


#check trivial

def elem_fun (x : X) : unit → X := 
λ _, x 

#check elem_fun

#check elem_fun ff
#check elem_fun tt 




end PROOFS