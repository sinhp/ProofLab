/-  Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------

# Unbundled Structures 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec8_structure_bundled



namespace PROOFS 


namespace STR  --nested inside the namespace PROOFS

variables {X Y Z : Type}
variable {f : X → Y}


/- The unbundled definition of preorder: this is the type of preorder structure on  a type `X`. Note that this structure depends on the parameter `X` in contrast with the bundles version which does not have any parameters. -/

structure preorder_unbundled (X : Type) :=
(rel : X → X → Prop)
(rflx : reflexive rel) 
(trns : transitive rel)

#check preorder_unbundled
#check preorder_bundled


#check preorder -- a function which assigns to every type `X` the type of preorder structures on `X` 


def preorder_unbundled_nat_eq : preorder_unbundled ℕ := 
{
  rel := λ m, λ n, m = n, 
  rflx := by {unfold reflexive,intro x, refl, },
  trns := by {unfold transitive, apply eq.trans,}, 
}

#check preorder_unbundled_nat_eq 
#print preorder_unbundled_nat_eq

#reduce preorder_unbundled_nat_eq.rel 
#reduce preorder_bundled_nat_eq.rel 



def preorder_unbundled_nat_le : preorder_unbundled ℕ := 
{
  rel := λ m, λ n, m ≤ n, 
  rflx := by {unfold reflexive,intro x, refl, },
  trns := by {unfold transitive, apply le_trans,}, 
}




#check preorder

def preorder_unbundled_bool_le : preorder_unbundled bool := 
{
  rel := λ b, λ b', b && b' = b,
  rflx := by { unfold reflexive, -- 
               intro x, --   
               cases x, 
               repeat {refl}, 
               },
  trns := by { unfold transitive, 
               intros x y z, 
               intros h₁ h₂, rw ← h₁, rw bool_and_assoc, rw h₂}, -- prove some associativity of && and use it here. 
}



structure preorder_unbundled.morphism {X : Type} {Y : Type} (P : preorder_unbundled X) (Q : preorder_unbundled Y) := 
( to_fun :  X → Y ) -- a function between the carrier types
( respect_rel : ∀ {x₁ x₂ : X}, P.rel x₁ x₂ → Q.rel (to_fun x₁) (to_fun x₂) ) -- property which says that the relations between elements of X are respected by the function `f`

#check @preorder_unbundled.morphism


def preorder_unbundled.morphism.nat_eq_to_nat_le : preorder_unbundled.morphism  preorder_unbundled_nat_eq preorder_unbundled_nat_le := 
{
  to_fun := id, 
  respect_rel := by {
                      intros a b, 
                      intro h, 
                      dsimp, 
                      apply le_of_eq h, 
                    },
}









namespace ptwise
lemma left_inv {g : Y → X} {f : X → Y} (h : g ∘ f = id) :
  ∀ x : X, g (f x) = x :=
begin
  intro x, 
  apply congr_fun h, 
end 
end ptwise 


#check ptwise.left_inv







/-! ## Equivalence of types -/

-- the type of endomorphisms of `A`
def endo (A : Type)  := A → A  

#check endo


def id_A {A : Type} : endo A := id

/- `fun_equiv` (function equivalence) is the type of functions from `X → Y` with a two-sided inverse -/ 
structure fun_equiv (X : Type) (Y : Type) :=
(to_fun    : X → Y)
(inv_fun   : Y → X)
(left_inv  : inv_fun ∘ to_fun = id) -- i.e. inv_fun ∘ to_fun = id_X
(right_inv : to_fun ∘ inv_fun = id) -- i.e. to_fun ∘ inv_fun = id_Y

-- infix ` ≃ `:15 := fun_equiv

/-- 
`X ≃ Y` is the type of functions from `X → Y` with a two-sided inverse. 
or just the type of all equivalences between X and Y
-/


-- the type of automorphisms of `A`
def auto (A : Type)  := fun_equiv A A 

/-
Every automorphism is an endomorphism. 
-/

def endo_of_auto {A : Type} (α : auto A) : 
  endo A := 
α.to_fun



#check @endo_of_auto


def auto.action {A : Type} : auto(A) × A → A := 
uncurry endo_of_auto 


def auto.id {A : Type} : auto(A) := 
{
  to_fun := id, 
  inv_fun := id, 
  left_inv := by {refl,}, -- id ∘ id = id
  right_inv := by {refl,}, -- id ∘ id = id
}

def auto.inv {A : Type} : auto(A) → auto(A) := 
λ α, 
{
  to_fun := α.inv_fun,  
  inv_fun := α.to_fun, 
  left_inv := α.right_inv, 
  right_inv := α.left_inv, 
}


def auto.mul {A : Type} : auto(A) → auto (A) → auto(A) := 
λ α, λ β, 
{
  to_fun := β.to_fun ∘ α.to_fun, 
  inv_fun := α.inv_fun ∘ β.inv_fun,  
  left_inv := by {rw ← comp_assoc, nth_rewrite 1 comp_assoc, rw β.left_inv, simp, rw α.left_inv,},
  right_inv := by {funext, simp [ptwise.left_inv (α.right_inv), ptwise.left_inv (β.right_inv)], }
  -- or, -- by {funext, dsimp, rw ptwise.left_inv (α.right_inv), rw ptwise.left_inv (β.right_inv),  },  
} 



end STR 

end PROOFS