/-
Gaussian Integers : The Norm
Sina Hazratpour
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2022
-/

import ..prooflab
import .lec12_gaussian_integers

namespace PROOFS
namespace STR


@[protect_proj]
class has_nat_cast (R : Type) :=
(nat_cast : ℕ → R)

@[simp]
instance : has_nat_cast ℤ[i] := ⟨λ n,  ⟨n , 0⟩⟩

@[simp]
instance : has_int_cast ℤ[i] := ⟨λ n, ⟨n ,0⟩ ⟩ 


#check 2 + 3
#eval 2 + 3 

#check (2 : ℤ[i]) + 3 



@[simp] instance : has_coe_to_sort ℤ (ℤ[i])  := ⟨has_int_cast.int_cast⟩ 


#check @coe ℤ ℤ[i]  


@[simp]
lemma coe_mk {x : ℤ} : 
  (x : ℤ[i]).re = x := 
begin
  refl, 
end 



#eval (⟨1, 1⟩ : ℤ[i]) + 3
#eval (3 : ℤ[i])+ (⟨1, 1⟩ : ℤ[i])



@[simp]
lemma int_cast_re {n : ℤ} : 
  (n : ℤ[i]).re = n := 
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
  simp, 
end 



/- Now we have all the tools to prove that the function `int_cast` is indeed a multiplicative monoid morphism.-/


class mult_monoid.morphism (M : Type) (N : Type) [mult_monoid_str M] [mult_monoid_str N] :=
(to_fun : M → N)
(resp_one : to_fun 1 = 1)
(resp_mul : ∀ x y : M, to_fun (x * y) = to_fun x * to_fun y)


infixr ` →ₘ* `:25 := mult_monoid.morphism

instance : ℤ →ₘ* ℤ[i] := 
{ to_fun := λ x, x,
  resp_one := by {refl, },
  resp_mul := by {intros x y, ext; simp } }





-- conjugate of a Gaussian integers
@[simp]
def conj (z : ℤ[i]) : ℤ[i] := ⟨z.re, -z.im⟩ 

#check conj

#eval conj ⟨0 , 1⟩ 
#eval conj 1 



/- We show that conjugation gives rise to a multiplicative monoid morphism. -/


def conj_mon_map : ℤ[i] →ₘ* ℤ[i] := 
{ 
  to_fun := λ z, conj z,
  resp_one := by {refl},
  resp_mul := by {intros z w, ext; simp, rw add_comm,}
}

#check conj_mon_map


def conj_mon_map_alt : ℤ[i] →ₘ* ℤ[i] := 
{ 
  to_fun := λ z, conj z,
  resp_one := by {refl},
  resp_mul := by {
                    intros z w, 
                    ext, 
                    {
                      calc (conj (z * w)).re = (z * w).re : sorry 
                      ...                    = z.re * w.re - z.im * w.im : sorry 
                      ...                    = (conj z).re * (conj w).re - (conj z).im * (conj w).im  : sorry
                      ...                    = (conj z * conj w).re : sorry, 
                     },
                    {
                      sorry,
                    },
  },
}




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



/-- The `norm` of `x = a + bi` is defined as `a^2 + b^2`. -/
@[simp]
def norm (z : ℤ[i]) := (z.re)^2 + (z.im)^2

#check norm 

#eval norm ⟨0,1⟩ 
#eval norm ⟨1,0⟩ 
#eval norm ⟨1,3⟩ 

@[simp]
lemma def_norm {x y : ℤ}: 
  norm (⟨x, y⟩ : ℤ[i]) = x^2 + y^2 := 
begin 
  refl, 
end 





lemma norm_int (z : ℤ) : 
  norm (int_cast z) = z^2 := 
begin
  simp, 
end   




lemma norm_eq_mul_conj (z :  ℤ[i]) : 
  z * (conj z) = norm z :=
begin 
  ext; simp,    
end   




theorem norm_conj (z : ℤ[i]) : norm (conj z) = norm z :=
by { simp, sorry}






theorem norm_mul (z w : ℤ[i]) : 
  norm (z * w) = norm z * norm w :=
begin
  sorry,  
end 






#check ring




instance : comm_ring ℤ[i]  :=
{ zero := 0,
  one := 1,
  add := (+),
  neg := λ x, -x,
  mul := (*),
  add_assoc := gaussian_int.add_assoc,
  zero_add := by { intros, ext; simp },
  add_zero := by { intros, ext; simp },
  add_left_neg := by { intros, ext; simp },
  add_comm := by { intros, ext; simp; ring },
  mul_assoc := by { intros, ext; simp; ring },
  one_mul := by { intros, ext; simp },
  mul_one := by { intros, ext; simp },
  left_distrib := by { intros, ext; simp; ring },
  right_distrib := by { intros, ext; simp; ring },
  mul_comm := by { intros, ext; simp; ring }
   }



end STR 
end PROOFS
