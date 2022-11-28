/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# Basics of Categories
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

-- /-
-- "_Category theory takes a bird’s eye view of mathematics. From high in the sky, details become invisible, but we can spot patterns that were impossible to de- tect from ground level._" 

-- From "Basic Category Theory" by Tom Leinster
-- -/



-- import tactic.basic
import ..prooflab
import lectures.lec15_integers

namespace PROOFS
open PROOFS.STR


/-
We already have so far seen many interesting __objects__ in this course: 

- Types (introduced in lecture 1)
- Pointed Types (introduced in lecture 11)
- Propositions (introduced in lecture 1 and 6) and Predicates/Relations (introduced in lecture 7)
- Graphs (introduced in hackathon)
- Quasigroups (introduced HW 8)
- Semigroups 
- Monoids (natural numbers, endofunctions, endomorphism of monoids)
- Commutative monoids (a monoid where multiplication/addition operation is commutative, e.g. fake natural numbers `mat`, ℕ, ℤ, ℤ[i],  )
- Groups (introduced as an extension of the strucute of monoids (monoids with inverses), e.g. integers and gaussian integers ℤ[i], group of auto-functions (functions `X → X` which are equivalences.))
- Commutative rings (two operations (+, *), e.g. integers and gaussian integers)
-/


/-
In each case, we have seen how to __relate__ objects of the same kind by an appropriate notion of __map__ (also called  __morphism__) between them: 

- Function between types (`f : X → Y`, e.g. `bool_of_nat` relates `nat` to `bool`, `nat_of_bool`, many coercion functions, for instance from integers to Gaussian integers. )
- Pointed functions (i.e. functions which preserved the points of pointed type domain) (`f : (X, x : X) → (Y, y : Y)` where `f x = y`)
- Derivations of propositions (`P → Q` if we can derived `Q`from `P`)
- Graph homomorphism between graphs (they preserve adjacency relation)
- Monoid homomorphism between monoids (they preserve multiplication/addition operation)
- Group homomorphism between groups (they preserve multiplication/addition operation)
- Ring homomorphism between commutative rings (they preserve multiplication and addition operations)
-/ 

/-
Furthermore, we can __compose__ such maps. For instance in the Graph hackathon we composed homomorphisms of graphs and in HW10 you defined the composition of monoid morphisms.

Recall HW10.Q1 
@[simp]
def mult_monoid.morphism.comp (g : M →ₘ* N) (f : L →ₘ* M)  : L →ₘ* N := 
{ to_fun := g ∘ f,
  resp_one := sorry,
  resp_mul := sorry, } 

And in all of the above cases we established an __identity__ function or homomorphism for each object `X` which is netural with respect to composition. 
-/


/-
This common pattern can be generalized to the abstract notion of category_str. A __category_str__ consitsts of

1. a collection of __objects__,
2.  a collection of __morphisms__, (maps between objects)
3. a composition operation whereby we can compose simpler morphisms and build complex morphisms,
4. an operation which provides identiry morphism for each object in the category_str. 

And these data satisfy the axioms of __associativity__ and (left/right) __unitality__. 
-/


/-
Many of the categories one meets in practice have as objects types with some structure attached to them and as have as morphisms functions or homomorphisms (i.e. structure-preserving functions) between them. This is a good model to keep in mind at the outset. 

Therefore, a category_str may be viewed as consisting of objects bearing a certain kind of structure together with morphisms/mappings between such objects preserving that structure. 

For instance, in the rest of the course we shall construct the following categories: 

-- __Graph__ : the category_str of graphs and graph homomorphisms (the objects of this category_str are __simple graphs__, and morphisms are __graph homomorphisms__)
-- __Mon__ : the category_str of monoids and monoid homomorphisms (the objects of this category_str are monoids, and morphisms are monoid homomorphisms)
-- __Group__ : the category_str of groups and groups homomorphisms
-/


/-
However, there are categories which are not the categories of structures. We construct a category_str whose objects are natural numbers `1,2,3, ...` and whose morphisms are matrices. 
-/



/- ## Some Philosophical Remarks 
1. A category is a __system__ which has objects and relations between these objects. The objects do not live in isolation: morphisms bind them together.
2. What is more important is the relations (i.e. morphisms): In fact, two objects are the same if they have the same relations to all other objects. This is known as the __Yoneda Lemma__ which we shall discuss in the last lecture.  Therefore, an object in a category is fully determined by its relations to other objects. Note that this is a not necessarily true for other systems of objects and relations. Is it true for instance than an animal is fully determined by the total sum of its relation to all other animals (including oneself, c.f. being vs becoming).   
-/


/- 
A preliminary ad-hoc structure on the way to defining the category structure, containing only the data of hom-types, the operations of identity and composition. 
Later, we extend the structure of precategory_str to category_str.
-/

--library_note "category_str_theory universes"

universes v u -- this handles the distinction between small and large categories 

class precategory_str (obj : Type u) : Type (max u (v+1))  :=
(hom : obj → obj → Type v) -- for any two objects `X` and `Y` we have the type of morphisms between `X` and `Y` 
(id       : Π X : obj, hom X X) -- specifies identity morphism for all types 
(comp     : Π {X Y Z : obj}, (hom X Y) → (hom Y Z) → (hom X Z) )
-- ( id       : Π X : obj, hom X X )
-- ( comp     : Π {X Y Z : obj}, (hom Y Z) → (hom X Y) → (hom X Z) )


--#check precategory_str
--#print precategory_str


/-! #### notation remarks
There is a special notation for the morphisms in a category_str: if `X Y : C`, we write

-  `X ⟶ Y` for the type `hom X Y`  of morphisms from `X` to `Y`.  Note: X ⟶ Y is entirely different than the type X → Y of functions from `X` to `Y`.  
  (To enter the special arrow `⟶`, type `\h` or `\hom`, or hover over the symbol to see the hint.)

- `𝟙 X` is a the identity morphisms on `X` (i.e., a term of type `X ⟶ X`).  (To enter the special arrow `𝟙`, type `\b1` or hover over the symbol to see the hint.)

- If `f : X ⟶ Y` and `g : Y ⟶ Z`, then we write `g ⊚ f` for the composition, a morphism `X ⟶ Z`. -- this is composition in every category_str, not necessarily in the category_str of types
-/



infixr ` ⟶ `:10 := precategory_str.hom -- type as \h
notation `𝟙` := precategory_str.id -- type as \b1
-- infixr ` ⊚ `:80 := precategory_str.comp-- type as \oo

local notation f ` ⊚ `:80 g:80 := precategory_str.comp g f    -- type as \oo



section
variables {𝓒 : Type} [precategory_str 𝓒]
variables W X Y Z : 𝓒 -- terms of type C can be regarded as objects of precategory_str 𝓒
#check X ⟶ Y
variables f₀ f₁ : X ⟶ Y 
variables g₀ g₁ : Y ⟶ Z
#check 𝟙 X
#check f₀ ⊚ g₀ -- this does not type check because the composition goes the other way round.
#check g₀ ⊚ f₀ 
#check f₀ ⊚ g₁
#check g₁ ⊚ f₀
end 





/-
- Now, we add the axioms of __unitality__ and __associativity__ to extend the structure of a precategory_str to a category_str. 
- The typeclass `category_str C` describes morphisms associated to objects of type `C`.
-/



class category_str (obj : Type u) extends precategory_str.{v} obj :=
(id_comp' : ∀ {X Y : obj} (f : hom X Y), f ⊚ (𝟙 X)  = f . obviously) -- naming based diagrammatic order of composition
(comp_id' : ∀ {X Y : obj} (f : hom X Y), (𝟙 Y) ⊚ f = f . obviously)
(comp_assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
  (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f) . obviously)


#check category_str.id_comp'



/-
`restate_axiom` is a command that creates a lemma from a structure field discarding any auto_param wrappers from the type.
It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".
-/

restate_axiom category_str.id_comp'
restate_axiom category_str.comp_id'
restate_axiom category_str.comp_assoc'

/-
`restate_axiom` automates writing lemmas by hand. If we did not use `restate_axiom` then we had to prove a lemma like in below:

@[simp]
lemma id_comp {C : Type} [category_str C] {X Y : C} : 
  ∀  f : X ⟶ Y ,  (𝟙 X) ⊚ f = f  := 
begin
  intro f, 
  rw [category_str.id_comp' f],
end   

At any rate, we now have three lemmas which we can use for rewrite/substitution.
-/

#check category_str.id_comp -- this is a lemma made directly from the field ategory_str.id_comp' in the definition of category.
#check category_str.comp_id
#check category_str.comp_assoc

/-
We add the attributes `simp` so that the tactic `simp` works when using these lemmas to simplify the state of our proofs. 
-/
attribute [simp] category_str.id_comp category_str.comp_id category_str.comp_assoc
attribute [trans] precategory_str.comp






/--
A `large_category_str` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category_str of types, or the category_str
of groups, etc.
-/
abbreviation large_category_str (C : Type (u+1)) : Type (u+1) := category_str.{u} C
/--
A `small_category_str` has objects and morphisms in the same universe level.
-/
abbreviation small_category_str (C : Type u) : Type (u+1) := category_str.{u} C



/-! ## Category of Types
There is a large category of types where the objects are types and the morphisms are functions between types. -/
instance : large_category_str Type :=
{ 
  hom := λ X, λ Y, X → Y,
  id := λ X, id,
  comp := λ X Y Z, λ f, λ g, g ∘ f,
  id_comp' := by {intros X Y, intro f, refl},
  comp_id' := by {intros X Y, intro f, refl},
  comp_assoc' := by {
                      intros W X Y Z, 
                      intros f g h, 
                      refl,
                      --funext, 
                      --dsimp, 
                      --refl,} 
                    } 
}

/- Note that by the tactic `.obviously` we actually do not need to provide the proofs of three least fields `comp_id'` and  `comp_assoc'` and `comp_assoc'` since all of them follows simply from `refl`. -/ 

#check (𝟙 ℕ) ⊚ (𝟙 ℕ)

example  : 
  bool_of_nat ⊚ (𝟙 ℕ) = bool_of_nat := 
begin
  simp, 
end 



/-! ## Category of Pointed Types 
See lecture 11 for definitions of `→•` and pointed_type.id, or simply command+click below. 
-/ 

instance : large_category_str pointed_type :=
{ 
  hom := λ X, λ Y, X →• Y,
  id := λ X, pointed_type.id,
  comp := λ X Y Z, λ f, λ g, g ∘• f,
}


/-! ##  The Category of a Preorder
Every preorder can be seen as a small category where the objects are the elements/terms of the (underlying type) of the preorder and between two objects `x` and `y` there is a (unique) morphism iff `x ≤ y`. To do this we need some tools to see a proposition as the type of its proofs.  
-/

/- We use `plift` to lift a proposition to the type of its proofs -/
#check plift (0 = 0) -- this a type whose terms are proofs of `0 = 0`. 

#check ( ⟨ (rfl : 0 = 0) ⟩ : plift (0 = 0) ) -- Since `rfl` is a proof of `0 = 0` we can lift it up to a term `⟨ (rfl : 0 = 0) ⟩` of type `plift (0 = 0)`. 

-- For a proposition `P`, the terms of type `plift`


/- We use `ulift` to lift a proposition to the type of its proofs -/
#check ulift 



instance small_category {X : Type} [preorder X] : small_category_str X := 
{
  hom := λ x, λ y, (plift (x ≤ y) : Type), 
  id := λ x, ⟨ le_refl x ⟩, 
  comp := λ x y z, λ f, λ g, ⟨le_trans f.down g.down ⟩,
}



/-
+ There are many more categories which we shall introduce in the three remaining lectures: the category of graphs, the category of monoids, the category of groups, the category of rings, the category of vector spaces, and finally the category of categories! 

+ There are statements which are true in all these categories by virtue of  being a category. This is like saying for instance a city has a town-hall by virtue of being a city (that is, we don't know in which country that city is located, what is the population of that city, etc. we just know it is a city.) 

-/


variables {𝓒 : Type} [category_str 𝓒] {W X Y Z : 𝓒} {A : Type}


namespace category_str

#check category_str




lemma eq_comp {f g : X ⟶ Y} (e : f = g) (h : Y ⟶ Z) : 
  h ⊚ f = h ⊚ g :=
begin
-- we want to prove  `h ⊚ f = h ⊚ g`
  rw e, -- we sub `f` for `g`
end 

  

lemma comp_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (e : g = h) : 
  g ⊚ f = h ⊚ f :=
begin
  rw e, 
end 


example (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :  
(h  ⊚  (𝟙 Y ⊚ g)) ⊚  f = h ⊚ (g ⊚ f) :=
begin
  simp, 
end



structure equiv (X Y : 𝓒) :=
(to_mor    : X ⟶ Y)
(inv_mor   : Y ⟶ X)
(left_inv  : to_mor ⊚  inv_mor = (𝟙 Y) ) 
(right_inv : inv_mor ⊚ to_mor = (𝟙 X) )



/-
A morphism `f` is an __isomorphism__ if it has both a left inverse and a right inverse.
-/

def is_iso (f : X ⟶ Y) := 
∃ (g h : Y ⟶ X), (g ⊚ f = 𝟙 X) ∧ (f ⊚ h = 𝟙 Y)


/- ## Challenge:
Show that an instance of equivalence `f : X ≃ Y` gives rise to a pair of isomorphisms, i.e. both `f.to_mor` and `f.inv_mor` are isomorphisms.

Conversely, we can prove that every isomorphism gives rise to an equivalence. 
-/



/--
A morphism `f` is a __monomorphism__ if it can be cancelled when __postcomposed__:
`g ≫ f = h ≫ f` implies `g = h`.
-/
@[simp] 
def is_mono (f : X ⟶ Y) :=
∀ (W : 𝓒) (x₁ x₂ : W ⟶ X), (f ⊚ x₁ = f ⊚ x₂) →  (x₁ = x₂)

@[simp]
lemma cancel_mono {f : X ⟶ Y} (mf : is_mono f) {x₁ x₂ : W ⟶ X} : 
  (f ⊚ x₁  = f ⊚ x₂) ↔ x₁ = x₂ :=
begin
  split,
  {
    intro h,
    apply mf, 
    exact h,
  },
  {
    apply congr_arg,
  },
end 




/-
Dually, a morphism `f` is an __epimorphism__ if it can be cancelled when __precomposed__:
`g ⊚ f = h ⊚ f` implies `g = h`.
-/

def is_epi (f : X ⟶ Y) := 
∀ {Z : 𝓒} (g h : Y ⟶ Z), (g ⊚ f = h ⊚ f) → g = h




/- ## Challenge 
Show that every isomorphism is a monomorphism. 
-/


end category_str 

end PROOFS






