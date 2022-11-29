/- 
Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------

# A short introduction to type classes 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec10_surj_inj_fact


namespace PROOFS


namespace STR

-- the bundled structure of types with a point in them 
structure pointed_type := 
(type : Type)
(point : type)




#check unit 
#check unit.star
#check @unit.ext



local notation `𝟙` := unit -- type as \b1
local notation `⋆` := unit.star
#check ⋆ 



/- 𝟙 is a pointed type but `empty` is not.-/
def unit_ptd : pointed_type  := 
{
  type := 𝟙, -- if you change 𝟙 to `empty`, you cannot provide for the second field any longer. 
  point := ⋆,
}


#check unit_ptd




def bool_ptd : pointed_type := 
{
  type := bool, 
  point := ff, 
}


def nat_ptd : pointed_type := 
{
  type := ℕ, 
  point := 0, 
}


structure Q2 := 
(x : ℚ)
(y : ℚ)

def Q2_ptd : pointed_type := 
{
  type := Q2, 
  point := ⟨0,0⟩, 
}


def R3_ptd : pointed_type := 
{
  type := R3, 
  point := ⟨0,0,0⟩, 
}




namespace pointed_type
variables {A B : pointed_type}


/- The __product__ of two pointed types is a pointed type.

  The attribute `@[simps point]` in below  is a hint to `simp` that it can unfold the point of this definition. -/

@[simps point]
def product (A B : pointed_type) : pointed_type := 
{
  type := A.type × B.type,
  point := (A.point, B.point),   
}


#check product


#check product nat_ptd Q2_ptd
#check (product nat_ptd Q2_ptd).point
#eval (product nat_ptd Q2_ptd).point

#eval (product nat_ptd bool_ptd).point -- type classes help with this



@[ext]
structure morphism (A B : pointed_type) :=
(to_fun : A.type → B.type)
(resp_pt : to_fun A.point = B.point)


end pointed_type


#check pointed_type.product
#print pointed_type.morphism
#check @pointed_type.morphism.to_fun 




infix ` →• `:25 := pointed_type.morphism


namespace pointed_type
variables {A B C D : pointed_type}


@[simp]
def compose (g : B →• C) (f : A →• B) : A →• C :=
{
  to_fun := g.to_fun ∘ f.to_fun,  
  resp_pt := by {dsimp, rw f.resp_pt, exact g.resp_pt,},
}

def id : A →• A := 
{
  to_fun := id, 
  resp_pt := rfl, 
}

infixr  ` ∘• ` : 90  := compose


lemma comp_assoc {g : A →• B} {k : B →• C} {l : C →• D}: l ∘• (k ∘• g) = (l ∘• k) ∘• g :=
begin
  simp, 
end 

end pointed_type
end STR 






namespace type_classes 

variables X Y Z U V W : Type


/-! ### Inhabited types -/
-- @[class] structure has_element (X : Type) : Prop := (some_el : ∃ x : X, true)

-- This is an example of an unbundle type : the structure of all elements of `X`

@[class] -- the new bit
structure has_element (X : Type) :=
(el [] : X) -- el is a generic element of X, it has no other propetry than being an element of X. 


section 
#check has_element -- it is a function which provides for any type `X` the type of its elements 
#check has_element X -- the type of elements of X -- compare this to the example of upper bounds from HW7
#print has_element 
#check has_element.el 
#print has_element.el -- the [] bracket makes X  in Π (X : Type u_10) explicit.
end 


@[instance] -- the new bit
def natural : has_element ℕ :=
{ el := 0 }


/-
A shorthand for `@[instance] def` is `instance`. 
-/

instance integer : has_element ℤ := 
{ el := 0 }


instance boolean : has_element bool := 
{ el := ff }


instance unit : has_element unit := 
{ el := () }



instance list {X : Type} : has_element (list X):= 
{ el := [] }




namespace has_element
/- The product of two types, each with an element, has an element.-/
instance product {A B : Type} [has_element A] [has_element B] :
  has_element (A × B) :=
{
  el := (has_element.el A, has_element.el B), 
}


/-! ### Instance Synthesis  

**Based on the type, Lean retrieves the relevant instances.**

Whenever the elaborator is looking for a value to assign to an argument `?M` of type `has_element X` for some `X`, it can check the list for a suitable instance: For example, if it looking for an instance of `has_element nat` and `has_element bool`, it will find respectively `bool.has_element` and `nat.has_element`. 

Then Lean synthesizes these instances with the instance `prod.has_element` to know that the product `ℕ × bool` is nonempty. 
-/

section 
#check has_element (ℕ × bool)
#check has_element.el (ℕ × bool) -- how does Lean know that `ℕ × bool` has an elemnet? that is how does it know an instance of `has_element` structure for the type `ℕ × bool`? Well, `ℕ × bool` is a product type, so to have an instance `has_element` for it, Lean will look for an instance of `has_element` for product types which we defined above (see `product`). `prodcut` instance tells us that to have a  `has_element` structure for a product `A × B` it is enough to have a `has_element` structure for `A` and a `has_element` structure for `B`. But, in our situation `A` is `ℕ` and `B` is `bool`. So, Lean's task now is to find instances `has_element` structure for `nat` and for `bool` which are provided by `has_element.natural` and `has_element.boolean`. We actually do not need to provide any of these names explicitly in constructing an element of `ℕ × bool`; Lean's instance synthesis does it automatically for us.  
#eval has_element.el (ℕ × bool)
end 

-- we can do this by explicitly naming the instances of `has_element A` and `has_element B`, although this is against the automation spirit of using Lean. 
instance product_alt {A B : Type} [hA : has_element A] [hB : has_element B] :
  has_element (A × B) :=
{ el := ⟨hA.el, hB.el⟩ }


@[instance] def fun_from_empty {Y : Type} :
  has_element (empty → Y) :=
{ el := λ a : empty, match a with end }

#reduce has_element.el (empty → empty) 


class morphism (X Y : Type) [has_element X] [has_element Y] := 
(to_fun : X → Y) 
(resp_el : to_fun (has_element.el X) = has_element.el Y)



instance unit_to_bool : morphism unit bool := 
{ 
  to_fun := λ x, ff, -- try changing `ff` to `tt`. Does it work? why not? 
  resp_el := by {refl}, 
}


instance bool_to_nat : morphism bool nat := 
{ 
  to_fun := nat_of_bool, 
  resp_el := by {refl}, 
}


#check has_element.bool_to_nat



end has_element



end type_classes



end PROOFS 