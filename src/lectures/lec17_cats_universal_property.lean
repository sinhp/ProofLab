/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# Cats: Universal Properties
😺 🐈 😼 🐈‍⬛ 😸 🐈 🙀 😻 🐈 😹
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

/-
The most important concept in category theory is that of __universal property__. We already have seen an example of univeral property in construction of fake integers from fake natural numbers by __quotient__ in lecture 15. The quotient construction in the category of types. We will generalize the quotient construction to any category. 

The further you go in mathematics, especially pure mathematics, the more universal properties you will meet. We will spend most of our time studying different manifestations of this concept.
-/



-- import tactic.basic
import ..prooflab
import lectures.lec16_categories_basic


open PROOFS.STR


/-
Let's recall what categories are by giving some more examples of categories. 
-/


/-! # Delooping of a monoid 
Given a monoid `M` (i.e. a type equipped with a monoid structure), we construct a category which has only one object and `M` many morphisms. The composition of morphisms in this category is given by the monoid multiplication. 
-/



instance delooping (M : Type)[mult_monoid_str M] : small_category_str unit := 
{ 
  hom := λ _, λ _, M ,
  id := 1,
  comp := λ {_ _ _}, (*) ,
  id_comp' := by {intros _ _, intro f, simp [mult_mon_one_mul f],},
  comp_id' := by {intros _ _, intro f, simp [mult_mon_mul_one f],},
  comp_assoc' := sorry, 
}  








/-! # Terminal Object
-/










/-
Product
-/


#check prod

