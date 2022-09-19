/-
Algebra of Functions: Part II
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec3_function

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true




namespace PROOFS

variables {A B C X Y Z U V W : Type} 


/-! ### Functions evaluation


**Question**: What did all the functions we defined in the previous lecture have in common? 
















**Answer** : They all had one input and one output. 




We can __evaluate__ a function at an input by applying the function to it. 
-/

-- #eval double 7
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

def mul_square (m n : ℕ) := 
m * m * n * n

-- #check mul_square 
-- #check mul_square 1 


#check nat.add  
#check nat.mul
#check nat.le
#check int.add
#check int.mul
#check rat.add
#check rat.mul

def sum_square (m n : ℕ) := 
m * m + n * n

-- #check sum_square 
-- #check sum_square 1 
-- #check sum_square 1 2
-- #eval sum_square 1 2



def fst_fun (x : X) := 
λ (y : Y), x

-- What is the type of fst_fun? And what does it do?
#check fst_fun 


def fst_fun_alt (x : X) (y : Y) := 
x 
-- What is the type of fst_fun_alt? And what does it do?
-- #check fst_fun_alt


-- CHALLENGE: define the second projection
def snd_fun  : X → Y → Y := 
sorry 
-- #check snd_fun
section 
variables (x : X) (y : Y)
#check snd_fun x y
#eval snd_fun x y
end 


def fst (p : X × Y) := 
p.1

-- #check fst
-- #check fst
-- #check fst (1 , 2)
#eval fst (2, 1)


def snd (p : X × Y) := 
p.2



def pairing (f : Z → X) (g : Z → Y) (z : Z) : X × Y := 
(f z , g z) 



def pairing_alt (f : Z → X) (g : Z → Y)  := 
λ z, (f z , g z) -- abstracting over z with λ 


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
  sorry, 
end 



-- What does the function `bool_prod` do? 

def bool_prod : (bool → X) → X × X := 
sorry

-- #eval bool_prod switch 
-- eval 


-- What does the function `prod_bool` do? 

def prod_bool : X × X → (bool → X) := 
sorry

-- #eval prod_bool (1,2) ff






-- An example of a function which take a function as its argument

def evaluation (f : X → Y) (x : X) := f x
#check evaluation  
#eval evaluation double 3 

-- CHALLENGE: Write `evaluation` in the lambda notation. 


def curry : (X × Y → Z) → X → (Y → Z) :=
λ f, λ x, λ y, f (x , y)

def uncurry : (X → (Y → Z)) → (X × Y → Z) := 
sorry

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




/-! ### Equality of Functions -/

/-
Once we have defined functions (or anything) in Lean we can prove properties of them: For instance we might want to prove two functions are equal to each other.

- __Function Extensionality__ is a logical principle which says that we can prove any two functions `f : X → Y` and `g : X → Y`  (with the same domain and the same codomain) are equal (written as `f = g` ) if for all elements `x : X` we have a proof of `f x = g x`. In Lean, this is `funext`. Here's a little secret: `funext` is assumed in Lean so we do not need to be explicit about it when we use it. 
-/

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
  sorry, 
end   








example : 
  mul_square 1 = square := 
begin 
  ext a, 
  rw mul_square,
  rw square, 
  ring, 
end  








example : double = double_alt := 
begin 
sorry,  
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
linarith,  -- we cannot use `ring` here, since natural numbers do not form a ring (recall that a ring)  
end 



lemma fun_cong_two_args (a a' b b' : X)
    (f : X → X → X) (ha : a = a') (hb : b = b') :
  f a b = f a' b' :=
begin
  rw ha,
  rw hb,
end




example (a a' b b' : X)
    (f : X → X → X) (ha : a = a') (hb : b = b') :
  f a b = f a' b' :=
begin
  induction hb, induction ha, refl,
end







-- How many functions empty → bool 

-- How many functions unit → bool 





-- How many functions bool → bool 



-- How many functions bool → bool → bool 


-- How many functions (bool → bool) → bool


-- How many functions (bool → bool) → bool














#check empty.elim


#check unit
#print unit


#check trivial

def elem_fun (x : X) : unit → X := 
λ _, x 

#check elem_fun

#check elem_fun ff
#check elem_fun tt 


def bool_power_fun (f : X → Y) : (bool → X) → (bool → Y) := 
λ α, λ b, f (α b)


#check bool_power_fun switch
#check bool_power_fun switch switch
#check bool_power_fun switch switch ff
#eval bool_power_fun switch switch ff







end PROOFS