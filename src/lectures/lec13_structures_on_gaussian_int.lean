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




namespace gaussian_int 

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


end gaussian_int


/- Now we have all the tools to prove that the function `int_cast` is indeed a multiplicative monoid morphism.-/




@[ext]
class mult_monoid.morphism (M : Type) (N : Type) [mult_monoid_str M] [mult_monoid_str N] :=
(to_fun : M → N) -- f : M → N -- the underlying function of morphism
(resp_one : to_fun 1 = 1) -- f (1_M ) = 1_N
(resp_mul : ∀ x y : M, to_fun (x * y) = to_fun x * to_fun y) -- f(x *_M y) = (f x) *_N (f y)


infixr ` →ₘ* `:25 := mult_monoid.morphism


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

def is_constant {X Y : Type} (f : X → Y) := 
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


end gaussian_int

/- Two monoids `M` and `N` are __isomorphic__ if there is a monoid morphism `f : M →ₘ* N` whose undelying function is a bijection (or equivalently, an equivalence) -/


#check is_surjective
#check is_injective 


def is_bijective {X Y : Type} (f : X → Y) := 
is_surjective f ∧ is_injective f


structure mult_monoid.isomorphism (M : Type) (N : Type) [mult_monoid_str M] [mult_monoid_str N] := 
(mor :  M →ₘ* N) 
(bij : is_bijective mor.to_fun) 


infixr ` ≅ₘ* `:25 := mult_monoid.isomorphism


namespace gaussian_int


@[simp]
def idempotent {X : Type} (f : X → X) := f ∘ f = id


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



def conj_mon_map_iso {M : Type} :  
  ℤ[i] ≅ₘ* ℤ[i] := 
{ 
  mor := conj_mon_map,
  bij := by {split, sorry, sorry, }, 
}  




end gaussian_int













end STR 
end PROOFS 