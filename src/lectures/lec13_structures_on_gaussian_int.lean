/-
Gaussian Integers
Sina Hazratpour
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2022
-/

import ..prooflab
import .lec12_gaussian_integers

import data.int.basic



namespace PROOFS 
namespace STR 


class comm_mult_monoid_str (M : Type) extends mult_monoid_str M := 
(mul_comm : ∀ x y : M, x * y = y * x)


instance : comm_mult_monoid_str ℤ := 
{ 
  mul_comm := int.mul_comm,
} 

instance : comm_mult_monoid_str ℤ[i] := 
{ 
  mul_comm := gaussian_int.mul_comm,
} 



#check has_int_cast

--Defined in mathlib
-- class has_int_cast (R : Type) :=
-- (int_cast : ℤ → R)

@[simp] 
instance : has_int_cast ℤ[i] := ⟨ λ n, ⟨n, 0⟩  ⟩ 


-- @[protect_proj]
-- class has_nat_cast (R : Type) :=
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

/- Now we have all the tools to prove that the function `int_cast` is indeed a multiplicative monoid morphism.-/


class mult_monoid.morphism (M : Type) (N : Type) [mult_monoid_str M] [mult_monoid_str N] :=
(to_fun : M → N) -- f : M → N 
(resp_one : to_fun 1 = 1) -- f (1_M ) = 1_N
(resp_mul : ∀ x y : M, to_fun (x * y) = to_fun x * to_fun y) -- f(x *_M y) = (f x) *_N (f y)


infixr ` →ₘ* `:25 := mult_monoid.morphism


-- instance : ℤ →ₘ* ℤ[i] := -- a monoid morphism from integers to gaussian integers 
-- { 
--   to_fun := has_int_cast.int_cast,
--   resp_one := rfl,
--   resp_mul := by {intros x y, ext; simp,} 
-- } -- we need to prove more simp lemma 




instance : ℤ →ₘ* ℤ[i] := 
{ 
  to_fun := λ x, x,
  resp_one := by {refl, },
  resp_mul := by {intros x y, ext; simp, } 
}



-- instance : ℕ →ₘ* ℤ[i] := 
-- {
--   to_fun := λ x, x, 
--   resp_one := by {refl, },
--   resp_mul := by {intros x y, ext; simp, } 
-- }



-- conjugate of a Gaussian integers
@[simp]
def conj (z : ℤ[i]) : ℤ[i] := ⟨z.re, -z.im⟩ 

#check conj

#eval conj ⟨0 , 5⟩ 
#eval conj 1 



/- We show that conjugation gives rise to a multiplicative monoid morphism. -/


def conj_mon_map : ℤ[i] →ₘ* ℤ[i] := 
sorry 



end STR 
end PROOFS 