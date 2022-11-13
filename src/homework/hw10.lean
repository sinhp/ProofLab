/- 
Homeowork 10  
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec11_type_classes
import lectures.lec13_structures_on_gaussian_int



open PROOFS 
open PROOFS.STR 




variables {L M N : Type} [mult_monoid_str L] [mult_monoid_str M] [mult_monoid_str N]



/-! ## Question 1 (20 pts) 
First, show that monoid morphisms are closed under composition, i.e. the composition of two monoid morphisms is again a monoid morphism. 

Then, show that for any monoid `M`, the type of monoid endomorphism `M →ₘ* M` itself admits a monoid structure. Note that the latter is very different than the type of endofunctions `M → M`. we showed before that whereas there is only one constant endomorphism `ℤ →ₘ* ℤ` there are ℤ-mnay endofunctions `ℤ → ℤ`. 
-/

@[simp]
def mult_monoid.morphism.comp (g : M →ₘ* N) (f : L →ₘ* M)  : L →ₘ* N := 
{ to_fun := g ∘ f,
  resp_one := sorry,
  resp_mul := sorry, } 


infixr  ` ∘* ` : 90  := mult_monoid.morphism.comp

def mult_monoid.morphism.id : M →ₘ* M := 
{
  to_fun := id, 
  resp_one := by {simp}, 
  resp_mul := by {simp},
}

#check M →ₘ* M



instance : mult_monoid_str (M →ₘ* M) := 
{ 
  mul := (∘*),
  mul_assoc := sorry,
  one := mult_monoid.morphism.id,
  mul_one := sorry,
  one_mul := sorry, 
}





/-! ## Question 2 (20 pts) 
Construct the cartesian products of monoids, and show that the two projection are monoid morphisms .  
-/

instance mult_monoid_str.product {M N : Type} [mult_monoid_str M] [mult_monoid_str  N] :
  mult_monoid_str (M × N) :=
{ 
  mul := λ x, λ y, ⟨x.1 * y.1, x.2 * y.2⟩,
  mul_assoc := sorry,
  one := sorry,
  mul_one := sorry,
  one_mul := sorry, 
}


instance mon_fst : M × N →ₘ* M := 
sorry 


instance snd_fst : M × N →ₘ* N := 
sorry 





/-! ## Question 3 (20 pts) 
Construct an equivalence of types of gaussian integers ℤ[i] and the cartesian product ℤ × ℤ.   
-/
infix ` ≅ `:15 := fun_equiv

def gausssian_int_cartesian_product :  
  ℤ[i] ≅ ℤ × ℤ :=  
{ to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry, }  


/- Is this equivalence a monoid isomorphism? If yes, prove it in below, if no, explain why it is not. -/


def gausssian_int_cartesian_product_monoid_isomorphism : ℤ[i] ≅ₘ* ℤ × ℤ := 
sorry 






/-! ## Question 4 (20 pts) 
Show that the type of functions `X → M` has a monoid structure if the codomain `M` has a monoid structure. The multiplication on `X → M` is given by pointwise multiplication, i.e. the multiplication of two functions 
`f g : X → M` should be a function `f * g : X → M` where 
`f * g (x) = (f x) * (g x)`. 
-/

@[instance] 
def mult_monoid_str.function (X M : Type)  [mult_monoid_str  M] :
  mult_monoid_str (X → M) :=
{ 
  mul := sorry,
  mul_assoc := sorry,
  one := sorry,
  mul_one := sorry,
  one_mul := sorry,  
}







/-! ## Question 5 (20 pts) 
Show that `Prop` admit multiplicative and additive monoid structures. -/ 

instance : comm_mult_monoid_str Prop := 
{ 
  mul := (∧),
  mul_assoc := sorry,
  one := sorry,
  mul_one := by sorry,
  one_mul := by sorry, 
  mul_comm := sorry,
}


instance or_additive : comm_additive_monoid_str Prop := 
{ 
  add := (∨),
  add_assoc := sorry,
  zero := sorry,
  add_zero := by sorry,
  zero_add := by sorry, 
  add_comm := sorry,
}


instance xor_additive : comm_additive_monoid_str Prop := 
{ 
  add := λ P Q, (P ∨ Q) ∧ ¬ (P ∧ Q),
  add_assoc := sorry,
  zero := sorry,
  add_zero := by sorry,
  zero_add := by sorry, 
  add_comm := sorry,
}







/-! ## Question 6 (20 pts) 
For a type `X`, the type `set X` in Lean is defined as the function type `X → Prop`. Given a set `A : set X` 
(i.e. a function `A : X → Prop` and a term `x : X` we write `x ∈ A` as a shorthand for the proposition `A x`. 

  set X       X → Prop
----------|------------
    A     |   A : X → Prop
  x ∈ A   |   A x
-/

#check set

/- Show that the __convolution__ multiplication defined a semigroup structure on `set M` when `M` is a monoid.  -/

instance monoid_convolution_alt {M : Type} [mult_monoid_str M] :
  mult_semigroup_str (set M) := 
{ 
  mul := λ A B, λ m, ∃ x y : M, (m = x * y) ∧ (A x) ∧ (B y),  -- { (x * y) | (x ∈ A) (y ∈ B) }
  mul_assoc := sorry, 
}  





/- ## Question 7 (20 pts) 
In this problem we define the structure of __join semilattice__ in terms of commutative idempotent monoids. You then show that every join semilattice is in fact a preorder. 
-/

/-
A monoid is __idempotent__ if each of its elements is idempotent. 
-/

@[simp]
def idemp (e : M) := (e * e = e)

def mon_idemp (M : Type) [mult_monoid_str M] : Prop := 
∀ e : M, idemp e 


/- A __(join) semilattice__ is a commutative and idempotent additive monoid.  -/

@[class]
structure jslat_str (X : Type) extends comm_mult_monoid_str X := 
(idemp : mon_idemp X) 


/- 
Mathlib defines the notions of __preorder__ as a type class and it defined the structure of  __partial order__ as an extension of __preorder__ structure. Go ahead and examine this definitions by click&command in below. 
-/

#check preorder



def preorder_of_jslat (X : Type) [jslat_str X] : 
preorder X := 
{ le := λ x, λ y, (x * y = y),
  lt := sorry,
  le_refl := sorry,
  le_trans := sorry,
  lt_iff_le_not_le := sorry, }






/-! ## Question 8 (20 pts) 
Show that for any monoid morphism `f : M →ₘ* N` the image of the underlying function `f : M → N` inherits a monoid structure from `N`.  
-/


structure mult_monoid_image_fact (f : M →ₘ* N) := 
(node : Type)
(mon_node : mult_monoid_str node) 
(left_mor : M →ₘ* node)
(right_mor : node →ₘ* N) 
(fun_eq : right_mor ∘* left_mor = f)


local notation `im` :15 :=  fun_image 

instance mult_monoid_str.fun_image (f : M →ₘ* N) : mult_monoid_str (im f) := 
{ 
  mul :=  sorry,
  mul_assoc := sorry,
  one := sorry,
  mul_one := sorry,
  one_mul := sorry, 
}






/-! ## Question 9 (20 pts) 
In this problem, you are asked to construct image factorization for monoids using what you already did in the previous problem. You will show that for any monoid morphism `f : M →ₘ*  N` we can factor `f` into two monoid morphisms `p` and `m` such that `f = m ∘ p`, and `p` is surjective and `m` is injective.   
-/ 

def mon_mor_img_embedding (f : M →ₘ* N) : (im f) →ₘ* N := 
{ 
  to_fun := fun_image.embedding f, 
  resp_one := sorry,
  resp_mul := sorry,
}


def mon_mor_img_cover (f : M →ₘ* N) : M →ₘ* (im f) := 
{ 
  to_fun := fun_image.cover f,
  resp_one := sorry,
  resp_mul := sorry, 
}



def canonical_mult_monoid_image_fact (f : M →ₘ* N) : mult_monoid_image_fact (f : M →ₘ* N)  := 
{ 
  node := im f,
  mon_node := mult_monoid_str.fun_image f,
  left_mor := mon_mor_img_cover f,
  right_mor := mon_mor_img_embedding f,
  fun_eq := sorry,
}


