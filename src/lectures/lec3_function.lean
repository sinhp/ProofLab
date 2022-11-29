/-
Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------

# Algebra of Functions: Part I
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec2_algebraic_identities

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true




namespace PROOFS



variables {A B C X Y Z U V W : Type} -- "Let A B ... W be types". We are introducing types A ... W so that we do not have to repeat ourselves for each example/lemma/theorem context declration. 




/-! # Functions 
- Type of functions: In `lec0_intro.lean` we saw that given types `A` and `B` we can create new types. One of these new types is the function type `A → B`. For any types `A` and `B`, we can make a new type `A → B` called the __function type__ of `A` and `B`. The  elements of function types are __functions__.

- The idea of functions: A __function__ `f : A → B` is a program that takes an element `a : A` as an input argument and returns a unique element `f a : B` as output. We also say `f` "assigns" the element `fa` to an element `a`. And sometimes we say `f` "takes" or "maps" `a` to `f a`. 

- Domain and codomain: 
In the expression `f : A → B`, the object/type `A` is called the __domain__ (sometimes called __source__) of `f` and the object/type `B` the __codomain__ (sometimes called __tartget__) of `f`. 

- How to specify functions: 
Suppose we have a program/rule which outputs `b : B` for an input `a : A`. Note that `b` might depend on `a`. We represent this program as a function `λ a, b : A → B`. This is the so-called __function abstraction__. 

- How to use functions: 
This is the so-called function __application__ (aka __evaluation__). We'll talk more about this in a minute.
-- TODO: write more about lambda.
-/


/-! ## Some examples of functions -/

/- 
Let `double : ℕ → ℕ` be the function defined by `double (n) = 2 * n`:
-/ 
def double := 
λ n : ℕ, (2 * n) 
-- we use the symbol `:=` for defining functions in Lean. Whatever follows `:=` is the definition of the function. 


#check double 


-- all functions in Lean are __total__ which means we are not going to limit/constrain the input other than the limit/constraint by its type. 
def half := 
λ n, n/2 

#check half
#check half 1
#eval half 1
#eval half 2

#check 1/2
#check 1/(2:ℚ)
#check (1:ℚ)/2

def rational_one := (1 : ℚ)

#check rational_one/2

example : 
  rational_one/2 = 1/(2:ℚ) := 
begin
refl, 
end   

def half_neg := 
-- Lean interprets `n` to be an integer (the default way)
λ n, (-n : ℤ)/2 


def half_neg_alt := 
-- Lean interprets `n` to be a natural number since we told it so. 
λ n : ℕ , (-n : ℤ)/2 


#check half_neg


/-
 __Second way (non-lambda way) to specify functions__: Another way to specify the `double` function which avoids the lambda notation is as follows. This is somewhat closer to the way most mathematicians specify their functions. 

This way resembles the way we wrote lemmas/theorems.
-/ 
def double' (n : ℕ) := 
2 * n
#check double'
#reduce double'


def double_alt := 
λ n : ℕ, n + n 
-- syntactically this function is different than `double` and `double'`.
-- #check double_alt 



/- 
Let `square : ℕ → ℕ`  be the function defined by `square (n) = n * n`: 
-/
def square (n : ℕ) := 
n * n 
#check square
#eval square 3

/-
Let `g : ℚ × ℚ → ℝ` be the function defined by `g (x,y) = x^2 + y^2`.
-/

#check ((2.2 : ℚ), (1.7 : ℚ))
#eval  (2.2, 1.7)

#check (1/(3:ℚ), 7/(5:ℚ))

#check ( (1/3, 7/5) : ℚ × ℚ ) 

def rational_sum_of_squares (z : ℚ × ℚ) := 
(z.1)^2 + (z.2)^2


#eval rational_sum_of_squares (3/5, 4/5)


-- `.1` and `.2` are projections from the cartesian space `ℚ × ℚ` to `ℚ` which pick the first and second coordinates. 
#eval (52,4).1
#eval (52,4).2
#eval (52.3676,4.9041).1
#eval ( (52.3676,4.9041).1 : ℚ)

--#check real_sum_of_squares
--#eval real_sum_of_squares (1/2 , -1/2) 


-- __the third way__ of definition by __pattern matching__
def switch : bool → bool  
| tt := ff 
| ff := tt

#check bool
#check tt 
#check ff
#check switch 
#eval switch ff



-- We can also specify a function by assigning an output for each possible input. 
def nat_of_bool : bool → ℕ 
| ff := 0 
| tt := 1 


#check nat_of_bool
--#check nat_of_bool
--#eval nat_of_bool ff



-- __if ... then ... else ...__ style of definition
def bool_of_nat (n : ℕ) := 
if n = 0 then ff else tt

-- #check bool_of_nat



def int_of_nat : ℕ → ℤ := 
λ n , n 

#check int_of_nat



def self_of_nat (n : ℕ) := 
n

#check self_of_nat




def is_even (n : ℕ) := 
∃ k : ℕ, n = 2 * k 

#check is_even 

#check (0 = 1)





def is_odd (n : ℕ) := 
∃ k : ℕ, n = 2 * k + 1

#check is_odd


-- this where we ended on Wednesday. 


-- The absolute value function 
#check (abs : ℚ → ℚ)
#check (abs : ℝ → ℝ)
#check abs (-3 : ℚ)
#eval abs (-3 : ℚ)
#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)



/- CHALLENGE: define a function `distance_rat : ℚ → ℚ → ℚ` which takes two real numbers `x : ℚ ` and `y : ℚ ` as inputs and returns as output the standard Euclidean distance `| x - y |` between them. 
-/ 
def distance_rat (x y : ℚ) := 
abs(x - y)


#check int.nat_abs



#check abs
def distance_nat (x y : ℤ) := 
int.nat_abs ( x - y ) 


#check distance_rat
#check distance_nat


#check distance_nat (1/3) (1/2)
#eval distance_nat (1/3) (1/2)

#check distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should be a rational number
#eval distance_rat (3/2 : ℚ) (1/2 : ℚ) -- should evaluate to 1
#eval distance_rat (1/3) (1/2) -- should evaluate to 1







end PROOFS