/- 
Homeowork 8  
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec11_type_classes


/-! # Homework 8: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far. 
-/


variables {X Y : Type} {f : X → Y} {p : Y → X}


open PROOFS 
open PROOFS.STR 
open PROOFS.type_classes



local notation `𝟙` := unit -- type as \b1
local notation `⋆` := unit.star



lemma unit_unique (x : 𝟙) : 
   x = ⋆ := 
begin
  exact unit.ext,
end 


/- 
A map is __constant__ if it maps all points in the domain to the same point in the codomain.
-/
def is_constant (f : X → Y) := ∀ x x' : X, f x = f x' 

/- 
A map `f : X → Y` is __constant at a point__ `y` of `Y` if `f` maps all points in `X` to `y`. 
-/
def is_constant_at (f : X → Y) (y : Y) := ∀ x : X, f x = y

/-! ## Question 1 (20 pts):
Show that if a function is constant at a point then it is constant. 
-/
lemma constant_at_point_implies_constant {f : X → Y} :  
   (∃ y : Y,  is_constant_at f y)  → is_constant f := 
begin
  sorry, 
end  







/-! ## Question 2 (20 pts):
Prove that a function which factors through a type which is equivalent to the one-point type is constant. 

Feel free to use the lemma `ptwise.left_inv`
-/

#check @ptwise.left_inv

theorem constant_of_factor_unit  {f : X → Y} {Φ : fun_fact f} {α : fun_equiv Φ.node 𝟙} :  
   is_constant f :=
begin
   unfold is_constant, 
end 










/- For every type `X` there is a unique function 
from `X` to `𝟙` which takes all points of `X` to `⋆`. 
-/
@[simp]
def to_terminal (X : Type) : X → 𝟙 := λ x, ⋆

notation ` ! ` := to_terminal
infix ` ≅ `:35 := fun_equiv


/-! ## Question 3 (20 pts):
Prove that the unique function `X → 𝟙` is surjective iff `X` is pointed by filling the `sorry` placeholder. 
-/ 

def is_surj_of_pointed_type {X : pointed_type} : 
  is_surjective (! X.type) :=  
begin
   sorry, 
end 



/-
**Formalize the converse**, that is if `! X : X → 𝟙` is surjective then `X` is pointed (i.e. it admits the structure of a pointed type). Then **prove** the converse statement. 
-/




#check classical.some
noncomputable
def is_pointed_of_surj {X : Type} {h : is_surjective (! X)} : pointed_type :=
{
   type := X,
   point := let h' : (∃ x : X, true) := by {unfold is_surjective at h,
      simp at *, assumption} in classical.some h' , 
}








/-! ## Question 4 (20 pts):
Prove that the image of the unique function `X → 𝟙` is equivalent to to `𝟙` if `X` is pointed. 

Feel free to use the lemma `ptwise.left_inv`
-/

def truncation_of_pointed_type {X : pointed_type} : 
  𝟙  ≅ (fun_image (! X.type)) := 
{
  to_fun := sorry,
  inv_fun := sorry, 
  left_inv := by {sorry},
  right_inv := by {sorry},
}  





/- 
We say a type is __inhabited__ if there is some element in it. 
-/ 

@[simp]
def is_inhabited (X : Type) :=  ∃ x : X, true



/-
The __fibre at a point__ `x : X` of a function  `p : Y → X` is the preimage of `x` under `p`. 
-/
@[simp]
def fibre_at (x : X) := { y : Y // p y = x}

#check @fibre_at


local notation ` p⁻¹ ` : 15 := λ x, @fibre_at X Y p x
#check p⁻¹



/-!  ## Question 5 (20 pts): 
Let `p : Y → X` be a function. Prove that if all the fibres of `p` are inhabited then `p` is surjective.  
-/


def surj_of_pointed_fibres {ptd_fibres : ∀ x : X, is_inhabited (p⁻¹ x) } : is_surjective p := 
begin
   sorry,  
end 










