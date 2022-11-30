/- 
Homeowork 9  
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec11_type_classes
import lectures.lec12_gaussian_integers



open PROOFS 
open PROOFS.STR 


variables {X : Type} {P : X → Prop}



/- The first question is about __unique existence__. For instance, we know not only that there exists a natural `n` such that `n` is even and prime, but such a number is unique.  -/

-- ∃! is the symbol for unique existence. 

#check exists_unique


lemma uniquely_exists₁  : 
  (∃! x, P x) ↔ (∃ x, P x ∧ (∀ y : X, P y → y = x)) := 
begin
  rw exists_unique, 
end 


/-! ## Question 1 (20 pts): 
Give a proof of the following lemma. 
-/

lemma uniquely_exists₂  : 
  (∃! x, P x) ↔ (∃ x, P x) ∧ (∀ y z : X, P y ∧ P z → y = z) := 
begin
  sorry, 
end 






/- Questions 2 and 3 concern the notion of quasigroup.  In below we define __quasigroup__ structures. A quasigroup structure consists of one binary operation `op` operations and left and right divisions (with respect `op` ). 
-/

class quasi_group_str (Q : Type) := 
(op : Q → Q → Q) -- a binary operation `op` on `Q` 
(left_div : Q → Q → Q)  
(right_div : Q → Q → Q) 
(l := left_div) -- temporary notation, just inside this structure declaration
(r := right_div) -- temporary notation, just inside this structure declaration 
(op_of_left_div : ∀ x y : Q, op x  (l x y) = y) -- finding column 
(left_div_of_op : ∀ x y : Q, l x (op x y) = y) -- unique column 
(op_of_right_div : ∀ x y : Q, op (r y x)  x = y)
(right_div_of_op : ∀ x y : Q, r (op y  x) x  = y)



local infix `#` :15 := quasi_group_str.op
local infix ` \\ ` :15 := quasi_group_str.left_div -- `l x y` is `x \\ y`
local infixl ` // ` :15 := quasi_group_str.right_div -- `r x y` is `y // x` 


/-! ## Question 2 (20 pts):
Show that The integers ℤ with subtraction form a quasigroup. 
-/
instance : quasi_group_str ℤ := 
{ 
  op := λ x, λ y, x - y,
  left_div := sorry,
  right_div := sorry,
  op_of_left_div := sorry,
  left_div_of_op := sorry, 
  op_of_right_div := sorry, 
  right_div_of_op := sorry, 
}






/-! ## Question 3 (20 pts)
**(Part I)** :
 Prove the following simplification lemmas directly from the definitions above. 
-/

@[simp]
lemma mul_of_left_div_def {Q : Type} [quasi_group_str Q] (a b : Q) : 
  (a # (a \\ b)) = b := 
begin
  sorry, 
end 


@[simp]
lemma left_div_of_mul_def {Q : Type} [quasi_group_str Q] (a b : Q) : 
  (a \\ (a # b)) = b := 
begin
  sorry, 
end 


lemma mul_of_right_div_def {Q : Type} [quasi_group_str Q] (a b : Q) : 
  ((b // a) # a) = b := 
begin
  sorry, 
end 


lemma right_div_of_mul_def {Q : Type} [quasi_group_str Q] (a b : Q) : 
  ((b # a) // a) = b := 
begin
  sorry,
end 



/- 
## Question 3 (Part II): 
 Prove the Latin square property of quasigroups. A __Latin square__ is an array filled with different symbols, each occurring exactly once in each row and exactly once in each column. 
An example of a `3×3` Latin square with symbols `A B C` is

                      A	B	C
                      C	A	B
                      B	C	A

Hint : Q1 should help you here.                       
-/

theorem Latin_square_property {Q : Type} [quasi_group_str Q] : 
  ∀ a b : Q, (∃! x : Q, (a # x) = b) ∧ (∃! y : Q, (y # a) = b) := 
begin
  sorry,
end    







/- The notion of __monoid__ strucutre (`mult_monoid_str` and `additive_monoid_str`) was defined in lecture 12. -/

@[ext]
structure positive_nat := 
(num : ℕ)
(pos : 0 < num)




local notation ` ℕ₊ `: 15 := positive_nat

/- Fill in `sorry` placeholder in below.-/
instance : has_one ℕ₊ := sorry 


@[simp] 
lemma pos_nat_one_val : (1 : ℕ₊).num = 1 := 
begin
  sorry,  
end 

/- Fill in `sorry` placeholder in below.-/
instance : has_mul ℕ₊ := sorry




/-! ## Question 4 (20 pts):
Show that the positive natural numbers admit a multiplicative monoid structure fy filling in the `sorry` placeholders in below. You should use the instances of type classes `has_one ℕ₊` and `has_mul ℕ₊` in above. Feel free to prove your own simplification lemmas if needed.  
-/

instance : mult_monoid_str ℕ₊ := 
{ mul :=  sorry,
  mul_assoc := sorry,
  one := sorry,
  mul_one := sorry,
  one_mul := sorry,
}






/-!  In below we define the __group__ structure. A group structure on a type `X` consists of a binary operation (e.g. multiplication, addition) and a unary operation of taking __inverse__.  
-/

class additive_group_str (X : Type) extends additive_monoid_str X := 
(inv : X → X) 
(left_inv : ∀ x : X,  (inv x) + x =  0)
(right_inv : ∀ x : X,  x + (inv x) = 0)



class mult_group_str (X : Type) extends mult_monoid_str X := 
(inv : X → X) 
(left_inv : ∀ x : X,  (inv x) * x =  1)
(right_inv : ∀ x : X,  x * (inv x) = 1)

-- our notation for inverse of an element. 
postfix `ⁱ` :std.prec.max_plus := mult_group_str.inv  


section
variables (G : Type) [mult_group_str G] (x : G)
#check x
#check xⁱ
end 




/-! ## Question 5 (20 pts) : 
Show that the Gaussian integers with the opeation of addition form an additive group. -/


-- instance : additive_group_str ℤ[i] := 
-- { inv := has_neg.neg,
--   left_inv := by {intro x, ext; simp [gaussian_int.add_def]; simp [gaussian_int.neg_def],  },
--   right_inv := by {intro x, ext; simp [gaussian_int.add_def]; simp [gaussian_int.neg_def],  }, }




@[simp]
theorem add_im_def (x y : ℤ[i]) :
  (x + y).im = x.im + y.im :=
begin
  refl,
end


lemma gaussian_add_opposite {x : ℤ[i]} : -x + x = 0 :=
begin
ext,
rw gaussian_int.add_re_def,
rw gaussian_int.neg_def,
ring_nf,
rw gaussian_int.add_im_def,
rw gaussian_int.neg_def,
ring_nf,
end


instance : additive_group_str ℤ[i] := 
{ inv := has_neg.neg,
  left_inv := by { intro z,  rw gaussian_add_opposite,  },
  right_inv := by {intro x, ext; simp [gaussian_int.add_def]; simp [gaussian_int.neg_def],  }, }





/-
In below we define the notion of __monoid morphism__. A monoid morphism between monoids `M` and `N` is given by a function `f : M → N` which preserves the multiplication operation. 
-/

class mult_monoid.morphism (M : Type) (N : Type) [mult_monoid_str M] [mult_monoid_str N] :=
(to_fun : M → N)
(resp_one : to_fun 1 = 1)
(resp_mul : ∀ x y : M, to_fun (x * y) = to_fun x * to_fun y)


infixr ` →ₘ* `:25 := mult_monoid.morphism



/-! ## Question 6 (20 pts):
Show that the function from ℕ₊ → ℤ[i] which maps `n` to `n + 0i` is a multiplicative monoid morphism. 
-/

instance : ℕ₊ →ₘ* ℤ[i] := sorry 








/-! ## Question 7 (20 pts): 
Show that for a type `X` the automorphisms of `X` admits a group strucuture where the multiplication operation is given by the composition of functions. You might like to use some stuff we proved about `auto` in Lecture on unbundled strucutres. -/

def group_of_auto : mult_group_str (auto X) := 
sorry











/-! ## Question 8 (20 pts): 
Show that the endomorphisms of any type form a monoid with composition of functions as monoid multiplication. 
-/ 

instance monoid_of_endo : mult_monoid_str (endo X) := 
sorry 








/-! ## Question 9 (20 pts):
**Part I :** Prove the following lemma. 
-/
lemma inv_cancel_left {G : Type} [mult_group_str G] :
  ∀ a b : G, (aⁱ) * (a * b) = b := 
begin
  sorry 
end   


/-
**Part II :** Use the previous lemma to prove the following cancellation property of multiplication for groups. 
-/

lemma mul_left_cancel_group {G : Type} [mult_group_str G] :
  ∀ a b c : G, (a * b = a * c) → b = c := 
begin 
  sorry, 
end   





/- 
In below we define the __action__ of a monoid on a type. 
-/

class mult_monoid_action (M A : Type) [mult_monoid_str M] :=
(smul : M → A → A) -- the scalar multiplication of `M` on `A`. 
(one_smul : ∀ (x : A), smul (1 : M) x = x)
(mul_smul : ∀ (r s : M) (x : A), 
smul (r * s)  x = smul r (smul s x))


/- ## Question 10 (20 pts): 
Given a monoid `M` and an action of `M` on a type `A` construct a monoid morphism from `M` to `endo A`. 
-/ 


def monoid_morphism_of_monoid_action  (M A : Type) [mult_monoid_str M] [mult_monoid_action M A] : 
M →ₘ* (endo A) := 
{ to_fun := mult_monoid_action.smul ,
  resp_one := by {funext, rw mult_monoid_action.one_smul,  },
  resp_mul := sorry, }









