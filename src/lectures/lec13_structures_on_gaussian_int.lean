/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------

# Algebraic Structures on Gaussian Integers 
Sina Hazratpour
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2022
-/

import ..prooflab
import .lec12_gaussian_integers

import data.int.basic



namespace PROOFS 
namespace STR 

universe u

class comm_mult_monoid_str (M : Type u) extends mult_monoid_str M := 
(mul_comm : ∀ x y : M, x * y = y * x)


instance : comm_mult_monoid_str ℤ := 
{ 
  mul_comm := int.mul_comm,
} 


class comm_additive_monoid_str (M : Type u) extends additive_monoid_str M := 
(add_comm : ∀ x y : M, x + y = y + x)



namespace gaussian_int 

instance : comm_mult_monoid_str ℤ[i] := 
{ 
  mul_comm := gaussian_int.mul_comm,
} 

#check has_int_cast

--Defined in mathlib
-- class has_int_cast (R : Type u) :=
-- (int_cast : ℤ → R)

@[simp] 
instance : has_int_cast ℤ[i] := ⟨ λ n, ⟨n, 0⟩  ⟩ 


-- @[protect_proj]
-- class has_nat_cast (R : Type u) :=
-- (nat_cast : ℕ → R)
@[simp]
instance : has_nat_cast ℤ[i] := ⟨λ n,  ⟨n , 0⟩⟩ -- this works because of the coercion of nat to int


#check 2 + 3 

#check (2 : ℤ[i]) + 3 
#eval (2 : ℤ[i]) + 3 



@[simp]
lemma int_cast_re {n : ℤ} : 
  (n : ℤ[i]).re = n :=  -- proving an equality between integers 
begin
  refl, 
end 

@[simp]
lemma int_cast_im {n : ℤ} : 
  (n : ℤ[i]).im = 0 := 
begin 
  refl, 
end 



@[simp]
lemma nat_cast_re {n : ℕ} : 
  (n : ℤ[i]).re = n := 
begin 
  refl, 
end 


@[simp]
lemma nat_cast_im {n : ℕ} : 
  (n : ℤ[i]).im = 0 := 
begin 
  refl, 
end 


@[simp] 
lemma int_cast_mul {m n : ℤ} : 
 ((m * n) : ℤ[i]).re = m * n := 
begin
  simp, 
end 


@[simp] 
lemma mul_int_cast {m n : ℤ} : 
 (m : ℤ[i]) * (n : ℤ[i]).re = m * n := 
begin
  refl, 
end 


end gaussian_int


/- Now we have all the tools to prove that the function `int_cast` is indeed a multiplicative monoid morphism.-/




@[ext]
class mult_monoid.morphism (M : Type u) (N : Type u) [mult_monoid_str M] [mult_monoid_str N] :=
(to_fun : M → N) -- f : M → N -- the underlying function of morphism
(resp_one : to_fun 1 = 1) -- f (1_M ) = 1_N
(resp_mul : ∀ x y : M, to_fun (x * y) = to_fun x * to_fun y) -- f(x *_M y) = (f x) *_N (f y)

#check mult_monoid.morphism

infixr ` →ₘ* `:25 := mult_monoid.morphism


#check has_coe_to_sort

@[class]
structure mult_monoid  := 
(carrier : Type u) 
(str : mult_monoid_str carrier)


def bundle_up (M : Type u)[mult_monoid_str M] : mult_monoid := 
{
  carrier := M, 
  str := by apply_instance, 
}

#check bundle_up




#check has_coe_to_fun

variables {M N : Type u} [mult_monoid_str M] [mult_monoid_str N]





instance mult_monoid_to_sort_coe (M : Type u) : 
  has_coe (mult_monoid_str M) (Type u)  :=
⟨coe := M⟩




instance : has_coe_to_fun  (M →ₘ* N)  (λ _, M → N) := 
⟨λ f, f.to_fun ⟩  --defined based on the projection `.to_fun` of monoid morphism to function 

-- if we have a function between the underlying types of two multiplicative monoids and a proof that the function preserves `1` and `*` , then applying the coercion of the promotion is identity (i.e. it does nothing). 
@[simp] lemma coe_mk_mul_mor {f : M → N} {h_one : f 1 = 1} {h_mul: ∀ x y : M, f (x * y) = f x * f y} {x : M} :
  { mult_monoid.morphism . to_fun := f, resp_one := h_one, resp_mul := h_mul } x = f x := 
begin
  refl, 
end

@[simp] 
lemma coe_mul_resp (f : M →ₘ* N) (x y : M) :
  f (x *  y) = f x * f y := 
begin
  apply mult_monoid.morphism.resp_mul, 
end   


@[simp] 
lemma coe_mul_one (f : M →ₘ* N) :
  f 1 = 1 := 
begin
  apply mult_monoid.morphism.resp_one, 
end  



/-
⇑f and ↥M are notations for coe_fn f and coe_sort M. They are the coercion operators for the function and sort classes.

We can instruct Lean’s pretty-printer to hide the operators ↑ and ⇑ with set_option.
-/

lemma test (f : M →ₘ* N) (a : M) :
  f ((a * a) * a) = (f a * f a) * f a :=
begin 
calc
  f ((a * a) * a) = f (a * a) * f a : by 
  {rw [f.resp_mul (a * a) a], }
            ... = (f a * f a) * f a : by {rw [f.resp_mul]},

end 

#check @test
set_option pp.coercions false
#check @test






@[ext]
class additive_monoid.morphism (M : Type u) (N : Type u) [additive_monoid_str M] [additive_monoid_str N] :=
(to_fun : M → N) -- f : M → N -- the underlying function of morphism
(resp_zero : to_fun 0 = 0) -- f (1_M ) = 1_N
(resp_add : ∀ x y : M, to_fun (x + y) = to_fun x + to_fun y) -- f(x *_M y) = (f x) *_N (f y)


infixr ` →ₘ+ `:25 := additive_monoid.morphism
variables {A B : Type u} [additive_monoid_str A] [additive_monoid_str B]



instance : has_coe_to_fun  (A →ₘ+ B)  (λ _, A → B) := 
⟨λ f, f.to_fun ⟩  --defined based on the projection `.to_fun` of monoid morphism to function 

@[simp] 
lemma coe_mk_add_mor {f : A → B} {h_zero : f 0 = 0} {h_add : ∀ x y : A, f (x + y) = f x + f y} {x : A} :
  { additive_monoid.morphism . to_fun := f, resp_zero := h_zero, resp_add := h_add } x = f x := 
begin 
  refl,
end 






-- instance : ℤ →ₘ* ℤ[i] := -- a monoid morphism from integers to gaussian integers 
-- { 
--   to_fun := has_int_cast.int_cast,
--   resp_one := rfl,
--   resp_mul := by {intros x y, ext; simp,} 
-- } -- we need to prove more simp lemma 


namespace gaussian_int

instance int_cast_mon_morphism : ℤ →ₘ* ℤ[i] := 
{ 
  to_fun := λ x, x,
  resp_one := by {refl, },
  resp_mul := by {intros x y, ext; simp, } 
}

end gaussian_int


 -- there can be potentially many instances since we are looking for functions ℤ → ℤ which preserve 1 : ℤ and the * of ℤ. Is there a nontrivial monoid morphism  `ℤ →ₘ* ℤ` ? 
def mult_monoid_morphism_int_constant : ℤ →ₘ* ℤ := 
{ 
  to_fun := λ n, (1 : ℤ),
  resp_one := by {refl,},
  resp_mul := by {simp,},
}
-- Whereas we have ℤ-many constant functions ℤ → ℤ there is only one constant monoid morphism ℤ → ℤ, namely `mult_monoid_morphism_int_constant`. -- Challenge: let's prove there this claim. 

def is_constant {X Y : Type u} (f : X → Y) := 
∀ x x' : X, f x = f x'

#check is_constant 

lemma unique_monoid_morphism_int_constant : ∀ (f : ℤ →ₘ* ℤ),  is_constant (f.to_fun) → (f = mult_monoid_morphism_int_constant) := 
begin
  intro f, -- let's fix a monoid morphism f : ℤ →ₘ* ℤ
  intro hf, -- a hypothesis that the underlying function of `f` is a constant function
  let f₀ := f.to_fun,
  rw (rfl : f.to_fun = f₀) at hf, 
  unfold is_constant at hf,   
  ext, -- the extensionality of monoid morphism structure states that in order to prove two morphisms are the same it suffices to prove their underlying functions are the same. Lean automatically applies the function ext as well. 
  sorry, 
end 


namespace gaussian_int
-- conjugate of a Gaussian integers
@[simp]
def conj (z : ℤ[i]) : ℤ[i] := ⟨z.re, -z.im⟩ 

#check conj

#eval conj ⟨0 , 5⟩ 
#eval conj (⟨17, 6⟩ * ⟨4 , 6⟩)
#eval conj ⟨17, 6⟩ * (conj ⟨4, 6⟩)
#eval conj 1 



/- We show that conjugation gives rise to a multiplicative monoid morphism. -/


def conj_mon_map : ℤ[i] →ₘ* ℤ[i] := 
{ 
  to_fun := conj,
  resp_one := by {refl},
  resp_mul := by {intros z w, ext; simp, rw int.add_comm,}
}


#eval conj_mon_map.to_fun ⟨2,1⟩
#eval conj_mon_map ⟨2,1⟩ -- eval works only for functions.  -- this works now due to coercion `has_coe_to_fun` for the type `M →ₘ* N` declared above. 


end gaussian_int



/- Two monoids `M` and `N` are __isomorphic__ if there is a monoid morphism `f : M →ₘ* N` whose undelying function is a bijection (or equivalently, an equivalence) -/


#check is_surjective
#check is_injective 


def is_bijective {X Y : Type} (f : X → Y) := 
is_surjective f ∧ is_injective f


structure mult_monoid.isomorphism (M : Type u) (N : Type u) [mult_monoid_str M] [mult_monoid_str N] := 
(mor :  M →ₘ* N) 
(bij : is_bijective mor.to_fun) 


infixr ` ≅ₘ* `:25 := mult_monoid.isomorphism


namespace gaussian_int


@[simp]
def idempotent {X : Type u} (f : X → X) := (f ∘ f = id)


lemma conj_conj : 
  idempotent conj := 
begin 
  simp, 
  funext, 
  simp, 
  ext; refl, 
end 


#check auto 

def conj_auto : auto (ℤ[i]) := 
{ 
  to_fun := conj,
  inv_fun := conj,
  left_inv := conj_conj,
  right_inv := conj_conj, 
}



def conj_mon_map_iso {M : Type u} :  
  ℤ[i] ≅ₘ* ℤ[i] := 
{ 
  mor := conj_mon_map,
  bij := by {split, sorry, sorry, }, 
}  


end gaussian_int




/-!  In below we define the __group__ structure. A group structure on a type `X` consists of a binary operation (e.g. multiplication, addition) and a unary operation of taking __inverse__.  
-/

class additive_group_str (X : Type u) extends additive_monoid_str X := 
(inv : X → X) 
(left_inv : ∀ x : X,  (inv x) + x =  0)
(right_inv : ∀ x : X,  x + (inv x) = 0)



class mult_group_str (X : Type u) extends mult_monoid_str X := 
(inv : X → X) 
(left_inv : ∀ x : X,  (inv x) * x =  1)
(right_inv : ∀ x : X,  x * (inv x) = 1)

-- our notation for inverse of an element. 
postfix `ⁱ` :std.prec.max_plus := mult_group_str.inv  


section
variables (G : Type u) [mult_group_str G] (x : G)
#check x
#check xⁱ
end 












end STR 
end PROOFS 