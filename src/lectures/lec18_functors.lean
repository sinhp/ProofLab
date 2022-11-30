/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# Morphisms of Categories: Functors
😺 🐈 😼 🐈‍⬛ 😸 🐈 🙀 😻 🐈 😹
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import lectures.lec16_categories_basic


/-! ## Philosophical Remarks 
We mentioned that categories encompass many many mathematical structures. What is amazing is that categories, encompass categories too! Categories are themselves mathematical structures, and there is a good notion of "morphism between categories" which relates them. Such morphisms are called functors and they are very important in studying relating one field of mathematics to the other. For instance, in algebraic topology, we study spaces by their fundamental groups (or groupoids). ... 
-/



/-! ## Functors

Functors are homomorphism of categories, they are the way we mor one category into another. To introduce functors, we'll need a second category around.
-/

variables {𝓒 𝓓 : Type} [precategory_str 𝓒] [precategory_str 𝓓]

/-
We write a functor as `F : C ⥤ 𝓓`.
(Unlike categories, which are partially unbundled, a functor is "fully bundled",
containing the function on objects as field. This parallels the design for algebraic structures.)
-/

 
@[class]
structure prefunctor (𝓒 : Type) [precategory_str 𝓒] (𝓓 : Type) [precategory_str 𝓓] :=
(obj [] : 𝓒 → 𝓓) -- the object function of functor structure
(mor : Π {X Y : 𝓒}, (X ⟶ Y) → (obj X ⟶ obj Y)) -- the morphism function of functor structure

section
variable F : prefunctor 𝓒 𝓓 
#check F.obj 
#check F.mor
variables {X Y : 𝓒}
variable g : X ⟶ Y
#check F.mor g
end 


@[class]
structure functor (𝓒 : Type)(𝓓 : Type) [category_str 𝓒] [category_str 𝓓]
  extends prefunctor 𝓒 𝓓 : Type :=
(mor_id'   : 
∀ (X : 𝓒), mor (𝟙 X) = 𝟙 (obj X) . obviously)
(mor_comp' : 
∀ {X Y Z : 𝓒} (f : X ⟶ Y) (g : Y ⟶ Z), mor (f ⊚ g) = (mor f) ⊚  (mor g) . obviously)



example (F : C ⥤ 𝓓) (X : C) : F.mor (𝟙 X) = 𝟙 (F.obj X) :=
F.mor_id X

example (F : C ⥤ 𝓓) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : F.mor (f ≫ g) = F.mor f ≫ F.mor g :=
F.mor_comp f g

/-!
The identity functor is written as `𝟭 C`, and functor composition is written `⋙`.
-/
example (F : C ⥤ 𝓓) {X Y : C} (f : X ⟶ Y) : (𝟭 C ⋙ F).mor (f ≫ 𝟙 Y) = F.mor f :=
begin
  rw functor.comp_mor,
  rw functor.mor_comp,
  rw category_theory.functor.mor_id, -- yuck! we really should fix this
  rw functor.id_mor,
  rw functor.mor_comp,
  rw category_theory.functor.mor_id,
  rw category.comp_id,
  -- or just replace the entire proof with `by simp`
end


#check 

/-!
To build a functor `F : C ⥤ 𝓓` we need to specify four fields
* `obj : C → 𝓓`
* `mor : ∀ {X Y : C} (f : X ⟶ Y), obj X ⟶ obj Y`
* `mor_id'` and `mor_comp'`, expressing the functor laws.
-/

example {X : C} : C ⥤ Type* :=
{ obj := λ Y, X ⟶ Y,
  mor := λ Y Y' f g, g ≫ f,
  mor_id' := λ X, begin funext, simp, end,
  mor_comp' := λ X Y Z f g, begin funext, simp, end }

/-!
However Lean will automatically attempt to fill in the `mor_id'` and `mor_comp'` fields itself,
because these fields are marked with `auto_param`. This lets us specify a tactic to use to
try to synthesize the field.

(In fact, the whole category theory library started off as an experiment to see how far we could
push this automation.)
-/

example {X : C} : C ⥤ Type* :=
{ obj := λ Y, X ⟶ Y,
  mor := λ Y Y' f g, g ≫ f, }

/-!
Lean automatically checked functoriality here!
This was pretty easy: we just need to use `category.comp_id` and `category.assoc`.
The more powerful we make the `simp` lemmas, the more boring goals can be discharged automatically.

Most of the `auto_param`s appearing in mathlib so far are in the `category_theory` library,
where they are nearly all filled using the tactic `tidy`, which repeatedly attempts to use
one of a list of "conservative" tactics.

You can see what `tidy` is doing using `tidy?`:
-/

example {X : C} : C ⥤ Type* :=
{ obj := λ Y, X ⟶ Y,
  mor := λ Y Y' f g, g ≫ f,
  mor_id' := by tidy?,
  mor_comp' := by tidy? }

/-!
Sebastien's talk on differential geometry tomorrow will give another example of `auto_param` being used.

You can also watch me doing a speed-run https://youtu.be/oz3z2NSNY8c of Floris's "pointed mor" exercises
from yesterday, taking advantage of `auto_param`.
-/




/-
Category of (small) types:
-/


/-
Let's prove that injections are mono. 
-/





lemma Top.mono_iff_injective {X Y : Top.{u}} {f : X ⟶ Y} : mono f ↔ function.injective f :=
begin
  split; intro H,
  { intros x x' h,
    let g : Top.point ⟶ X := Top.const x,
    let g' : Top.point ⟶ X := Top.const x',
    change g punit.star.{u+1} = g' punit.star.{u+1},
    apply Top.hom_congr,
    resetI,
    rw ←cancel_mono f,
    ext,
    exact h },
  { constructor,
    intros α g h hh,
    ext a,
    apply H,
    exact Top.hom_congr hh a }
end
