/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# Basics of Categories
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

/-
-- "_Category theory takes a bird’s eye view of mathematics. From high in the sky, details become invisible, but we can spot patterns that were impossible to de- tect from ground level._" 

-- From "Basic Category Theory" by Tom Leinster
-- -/



-- import tactic.basic
import ..prooflab
import lectures.lec15_integers
import tactic.basic

open PROOFS
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

/-
In the mathematical language Lean, types are organized into a hierarchy of universe levels, with each level representing a different __universe__ of types that are considered to be of a certain size or complexity. This hierarchy allows for a more structured and well-defined approach to working with types, while __avoiding the inconsistencies and paradoxes that can arise from allowing for the existence of a type of all types__.

It is possible to define a type in Lean that represents the collection of all types, but this is done in a more carefully __controlled__ manner than simply allowing for the existence of a type of all types. Universe levels are consistency control parameters. 
-/
universes v u -- this handles the distinction between small and large categories -- universe variables are inserted in the order that they were declared.




class precategory_str (obj : Type u) : Type (max u (v+1))  :=
(hom : obj → obj → Type v) -- for any two objects `X : obj` and `Y : obj` we have the type `hom X Y` of morphisms between `X` and `Y` 
(id       : Π X : obj, hom X X) -- specifies identity morphism for all types 
(comp     : Π {X Y Z : obj}, (hom X Y) → (hom Y Z) → (hom X Z) )
-- ( id       : Π X : obj, hom X X )
-- ( comp     : Π {X Y Z : obj}, (hom Y Z) → (hom X Y) → (hom X Z) )

#check precategory_str
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
--#check f₀ ⊚ g₀ -- this does not type check because the composition goes the other way round.
#check g₀ ⊚ f₀ 
--#check f₀ ⊚ g₁
#check g₁ ⊚ f₀

end 


/-
- Now, we add the axioms of __unitality__ and __associativity__ to extend the structure of a precategory_str to a category_str. 
- The typeclass `category_str C` describes morphisms associated to objects of type `C`.
-/

class category_str (obj : Type u) extends precategory_str.{v} obj : Type (max u (v+1)) :=
(id_comp' : ∀ {X Y : obj} (f : hom X Y), f ⊚ (𝟙 X)  = f . obviously) -- naming based diagrammatic order of composition
(comp_id' : ∀ {X Y : obj} (f : hom X Y), (𝟙 Y) ⊚ f = f . obviously)
(comp_assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
  (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f) . obviously)


#check category_str.id_comp'


set_option trace.simp_lemmas true



instance : category_str ℕ := 
{ hom := λ x, λ y, plift (x ≤ y),
  id := λ x, ⟨ le_refl x ⟩,
  comp := λ x y z, λ f, λ g, ⟨le_trans f.down g.down ⟩,
  id_comp' := by {intros X Y f, simp},
  comp_id' := by {intros X Y f, simp},
  comp_assoc' := by {intros W X Y Z f g h, simp}, }





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




initialize_simps_projections category_str (to_precategory_str_hom → hom,
  to_precategory_str_comp → comp, to_precategory_str_id → id, -to_precategory_str)





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


namespace category_str

/-! ## Category of Types
There is a large category of types where the objects are types and the morphisms are functions between types. -/
instance cat_of_types : category_str Type* :=
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



#check category_str.cat_of_types.id_comp'

--#reduce category_str.cat_of_types.id_comp'

#reduce category_str.cat_of_types.id_comp' (λ x, (x + 1))


section 

variables (𝓒 : Type u) [category_str.{v} 𝓒] (X Y : 𝓒) (f : X ⟶ Y) -- let 𝓒 be a category and `f : X ⟶ Y` a morphism in it . 

#reduce category_str.id_comp' f

end --section 



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
  hom := λ X, λ Y, X →• Y, -- really X is (A, a)
  id := λ X, pointed_type.id, -- id: (A,a) ⟶ (A,a)  
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
#check ulift -- lifting types from one universe to a higher universe
#check plift -- lifting propositions to types



instance small_cat_of_preorder (X : Type) [preorder X] : small_category_str X := 
{
  hom := λ x, λ y, (plift (x ≤ y) : Type), 
  id := λ x, ⟨ le_refl x ⟩, 
  comp := λ x y z, λ f, λ g, ⟨le_trans f.down g.down ⟩,
}

def two_to_three :  1 ⟶ 2 := 
⟨one_le_two⟩ 

#check two_to_three 

#reduce category_str.comp_id' two_to_three 


#check category_str.small_cat_of_preorder

instance foo : small_category_str ℕ := 
category_str.small_cat_of_preorder ℕ 

#check category_str.foo.hom 2 3

#reduce category_str.foo.hom 2 3




section lifting_categories

variables (𝓒 : Type u)[category_str.{v} 𝓒]


universe u'
-- we can lift 𝓒 from universe `u` to a higher universe `u'`. 
instance ulift_cat : category_str.{v} (ulift.{u'} 𝓒) :=
{ hom  := λ X Y, (X.down ⟶ Y.down),
  id   := λ X, 𝟙 X.down,
  comp := λ _ _ _ f g, g ⊚ f }

-- We verify that this previous instance can lift small categories to large categories.
example (𝓢 : Type u) [small_category_str 𝓢] : large_category_str (ulift.{u+1} 𝓢) := 
by apply_instance

end lifting_categories



/-
+ There are many more categories which we shall introduce in the three remaining lectures: the category of graphs, the category of monoids, the category of groups, the category of rings, the category of vector spaces, and finally the category of categories! 

+ There are statements which are true in all these categories by virtue of  being a category. This is like saying for instance a city has a town-hall by virtue of being a city (that is, we don't know in which country that city is located, what is the population of that city, etc. we just know it is a city.) 

+ It is interesting to see which statements are true in an arbitrary category. If we construct something or prove a statement in an arbitrary category,then these constructions and statements and will be valid in every particular category, such as the category of types, groups, etc.  

+ In below, we shall introduce new definitions and prove statements which are valid in an arbitrary category. 
-/


variables {𝓒 : Type u} [category_str 𝓒] {W X Y Z : 𝓒} {A : Type}



/-! # Delooping of a monoid 
Given a monoid `M` (i.e. a type equipped with a monoid structure), we construct a category which has only one object and `M` many morphisms. The composition of morphisms in this category is given by the monoid multiplication. 
-/


instance delooping (M : Type u)[mult_monoid_str M] : small_category_str.{u} (punit : Type u) := 
{ 
  hom := λ _, λ _, M,
  id := 1,
  comp := λ _ _ _, (*),
  id_comp' := by {intros _ _ _, simp [mult_mon_one_mul], },
  comp_id' := by {intros _ _ _, simp [mult_mon_mul_one],},
  comp_assoc' := by {intros _ _ _ _ _ _ _,simp,}, 
}  

#check category_str.delooping
#check category_str.comp




-- A shorter proof
-- instance delooping (M : Type)[mult_monoid_str M] : small_category_str unit := 
-- { 
--   hom := λ _, λ _, M,
--   id := 1,
--   comp := λ _ _ _, (*),
--   id_comp' := by {simp},
--   comp_id' := by {simp},
--   comp_assoc' := by {intros _ _ _ ,simp}, 
-- }  


-- Even shorter using tactic `.obviously`

instance delooping_alt (M : Type)[mult_monoid_str M] : small_category_str unit := 
{ 
  hom := λ _, λ _, M,
  id := 1,
  comp := λ _ _ _, (*),
}  





/-
Conversely, in every category every object has, by virtue of being an object of a category, a monoid structure.  
-/

/- The type of __endomorphisms__ of an object X in category 𝓒 -/

def End (X : 𝓒) := X ⟶ X  

#check @End


#check mult_monoid_str

/- The __endomorphisms monoid__ of an object in a category-/
def monoid_of_object {𝓒 : Type}[small_category_str 𝓒] (X : 𝓒) : mult_monoid_str (X ⟶ X) :=  
sorry 





/-! ## Challenge: 
The endomorphisms monoid of the only object in `single_obj α` is equivalent to the original
     monoid α. -/
-- def to_End {M : Type} [mult_monoid_str M] : M ≃* End (_) :=
-- sorry







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
(right_inv : inv_mor ⊚ to_mor = (𝟙 X)  )


local notation ` ≅ `:85 := equiv



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



/-! ## Opposite Category 
If `𝓒` is a category, then `𝓒ᵒᵖ` is the __opposite category__, with objects the same but all arrows reversed. `𝓒ᵒᵖ` is the mirror image of `𝓒`. If `X ⟶ Y ⟶ Z` are morphisms in `𝓒ᵒᵖ` then `Z ⟶ Y ⟶ X`  are maps in `𝓒`. 

In below we give `𝓒ᵒᵖ` the structure of a category. See `opposite_cat`. 
-/

def opposite (𝓒 : Type u) : Type u := 𝓒


notation X `ᵒᵖ`:std.prec.max_plus := opposite X


/- The canonical map `𝓒 → 𝓒ᵒᵖ`. 
We need to write `op X` to explicitly move `X` to the opposite category-/
@[pp_nodot]
def op : 𝓒 → 𝓒ᵒᵖ := id 



/- The canonical map `𝓒ᵒᵖ → 𝓒`. -/
@[pp_nodot]
def unop : 𝓒ᵒᵖ → 𝓒 := id

section test 
variable XX : 𝓒 
#check op XX 
#check unop (op XX)

example  : 
  unop (op XX) = XX := rfl 

end  test

@[simp] 
lemma op_unop (X : 𝓒ᵒᵖ) : op (unop X) = X := rfl

@[simp] 
lemma unop_op (x : 𝓒) : unop (op X) = X := rfl


/- The type-level equivalence between a type and its opposite. -/
def equiv_to_opposite :  𝓒 ≅ 𝓒ᵒᵖ :=
{ 
  to_fun := op,
  inv_fun := unop,
  left_inv := by {ext, refl, },
  right_inv := by {ext, refl, }, 
}


instance opposite_cat {𝓒 : Type u} [category_str.{v} 𝓒] : category_str.{v} 𝓒ᵒᵖ :=
{ 
  hom := λ X, λ Y, (unop Y ⟶ unop X), -- informally, hom_{𝓒ᵒᵖ} X Y = hom_{𝓒} Y X
  id := λ X, 𝟙 (unop X),
  comp := λ X Y Z, λ f g, f ⊚ g,
  id_comp' := by {intros X Y f, simp,},
  comp_id' := by {intros X Y f, simp,},
  comp_assoc' := by {intros W X Y Z f g h, rw [comp_assoc'],} 
}




/-
The opposite of an arrow in `𝓒`.
-/
def hom.op  {X Y : 𝓒} (f : X ⟶ Y) : 
op Y ⟶ op X := f

/-
Given an arrow in `𝓒ᵒᵖ`, we can take the "unopposite" back in `𝓒`.
-/
def hom.unop {X Y : 𝓒ᵒᵖ} (f : X ⟶ Y) : 
unop Y ⟶ unop X := f


@[simp] 
lemma op_comp {X Y Z : 𝓒} {f : X ⟶ Y} {g : Y ⟶ Z} :
  hom.op (g ⊚ f) = hom.op f ⊚ hom.op g := 
begin 
  refl, 
end   

@[simp] 
lemma unop_comp {X Y Z : 𝓒ᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} :
  hom.unop (g ⊚ f) = hom.unop f ⊚ hom.unop g := 
begin 
  refl, 
end   



@[simp] 
lemma op_id {X : 𝓒} : hom.op (𝟙 X) = 𝟙 (op X) := 
begin
  refl, 
end 

@[simp] 
lemma unop_id {X : 𝓒ᵒᵖ} : hom.unop (𝟙 X) = 𝟙 (unop X) := 
begin
  refl, 
end 




end category_str 







