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






/-! # Terminal Object
-/










/-
Product
-/


#check prod

