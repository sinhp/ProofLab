/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------

# Surjective Injective Factorization 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec9_structure_unbundled


namespace PROOFS

namespace STR

variables {X Y : Type} {f : X → Y}



/-! ### Prelim 1: Extending Structures 
We can use the `extend` command to define a structure that adds fields to one or more existing structures.

In example `H2plus` we are extending the structure `R2` (of a previous lecture) by adding new properties, i.e. equations indicating the points belong to the upper half plane. 
-/


@[ext] 
structure H2plus_alt_alt := 
(x : ℝ)
(y : ℝ)
(y_pos : 0 < y )


section
variable a : H2plus_alt_alt 
#check a.x 
#check a.y 
#check a.y_pos 
end 


@[ext] 
structure H2plus_alt := 
( a : R2 )
( y_pos : 0 < a.y )



section
variable b : H2plus_alt
#check b.a
#check b.a.x 
#check b.a.y 
#check b.y_pos 
end 




@[ext] 
structure H2plus extends R2 :=
(y_pos : 0 < y ) -- data satisfying certian constraint


def Pt_p1p2 : H2plus := 
{
  x := 1, 
  y := 2, 
  y_pos := by {simp}, 
}


#print H2plus
#check H2plus.to_R2 -- this is an embedding which forgets the positivity property 
#check H2plus.to_R2 Pt_p1p2


-- the way to prove two points of `H2plus` are the same is essentially the same way as proving equality of points of `R2`. 
example (a b : H2plus) (hx : a.x = b.x) (hy : a.y = b.y) :
  a = b :=
begin
  ext, 
  repeat {assumption},
end





/-! ### Prelim 2: Comprehension Types
If we have a predicate `P : X → Prop` we can make `P` into a type `{ x : X // P x }` which consists of pairs whose first component is a term of `x : X` and the second component is a proof `hx : P x`. 
-/ 


#check is_even 



lemma ten_is_even :
  is_even 10 := 
begin
  unfold is_even,
  use 5, 
  refl,
end 


def Even_Num := { n : ℕ // is_even n } -- This type consists of pairs of a natural number and a proof that the natural number is even. -/

#check Even_Num
#reduce Even_Num -- this unfolds the predicate `is_even`



-- to construct a term of `{ x : X // P x }` we need to provide a __value__ `x` (a term `x : X`) and a __proof of property__ `Px`.



def my_even_num : Even_Num := ⟨10, ten_is_even⟩ -- generic pairing different than product type  
-- value `10` and a proof `ten_is_even` of the property `is_even 10`.


def your_even_num : Even_Num := ⟨8, by {use 4, refl} ⟩ 


def our_even_num : Even_Num := ⟨8, ⟨4, rfl ⟩⟩ 


-- for projecting out of a comprehension, we use `.val` 
example (e : Even_Num) : ℕ := e.val -- here `e.val` is just a natural number, it has forgotten the evenness of `e`.



#check my_even_num.val
#eval my_even_num.val
#reduce my_even_num.prop



example (e : Even_Num) : 
  is_even e.val := 
begin
  exact e.prop,
end 


example (e e': Even_Num) (h : e = e') :
  e.val = e'.val := 
begin
  rw h, 
end 



-- two terms of `{ x : X // P x }` are equal if their corresponding values are equal. 
example (e e': Even_Num) (h : e.val = e'.val) :
  e = e' := 
begin
  ext, -- now we only need to prove e and e' are equal simply __as natual numbers__ (coercion to ℕ indicated by an arrow in the displayed goal. `↑e` is the same as `e.val`) 
  exact h,
end 




def fun_image (f : X → Y) : Type := { y : Y // ∃ x : X, y = f x}


#check @fun_image

#check fun_image nat_of_bool



def my_nat_of_bool : fun_image nat_of_bool := ⟨0, by {use ff, refl} ⟩ 
def your_nat_of_bool : fun_image nat_of_bool := ⟨0, ff, rfl ⟩ -- unbiased pairing (it is not left nor right binding) -- `rfl` is the proof that `ff` is mapped to `0`. 




-- factorization
structure fun_fact {X Y : Type} (f : X → Y) := 
(node : Type) -- the node through which `f` factors 
(left_fun : X → node) -- the left factor 
(right_fun : node → Y) -- the right factor 
(fun_eq : right_fun ∘ left_fun = f) 

#print fun_fact
#check @fun_fact.node
#check @fun_fact.left_fun
#check @fun_fact.right_fun 





@[simp]
def fun_image.embedding (f : X → Y) (z : fun_image f) : Y := z.val 

#check @fun_image.embedding

#check fun_image.embedding nat_of_bool




lemma inj_of_fun_image  (f : X → Y) : 
  is_injective (fun_image.embedding f) := 
begin
  simp, 
  intros y₁ y₂, 
  intro h₁, 
  ext, 
  exact h₁, 
end 



def fun_image.cover (f : X → Y) (x : X) : fun_image f := ⟨f x, x , rfl⟩ 


/- 
Recall that in order to extract a witness `x` and proof `hx : P x` from a hypothesis `h : ∃ x, P x`, we use the tactic `cases h with x hx`. 
-/

lemma surj_of_fun_image  (f : X → Y) : 
  is_surjective (fun_image.cover f) := 
begin
  unfold is_surjective, -- our goal is to prove that the function `fun_image.cover f` is surjective. We unfold the definition of surjectivity. 
  intro y, -- We have to show for every `y` in  `fun_image.cover f` there is some `x` in `X` such that `cover f x = y`
  cases y, -- an element `y` in  `fun_image.cover f` is some `y_val` in `Y` and a proof  `y_prop` of the fact that `∃ (x : X), y_val = f x`. 
  cases y_property with x h, -- from `y_prop`, by existentional elimination, we can find some `x : X` and a proof `h : y_val = f x`.   
  unfold fun_image.cover, -- simplifying definition of fun_image.cover. 
  use x, -- we find our desired `x`, from one before last step. 
  simp, -- simplifying the goal 
  rw h,  -- 
end 




structure surj_inj_fact {X Y : Type} (f : X → Y) extends fun_fact f := 
(surj : is_surjective left_fun)
(inj : is_injective right_fun)


def canonical_surj_inj_fact {X Y : Type} (f : X → Y) : surj_inj_fact f := 
{ 
  node := fun_image f, 
  left_fun := fun_image.cover f, 
  right_fun := fun_image.embedding f, 
  fun_eq := by {funext x, simp, refl},
  surj := by {exact surj_of_fun_image f,}, 
  inj := by {exact inj_of_fun_image f,}, 
}


#check @canonical_surj_inj_fact

end STR 
end PROOFS 