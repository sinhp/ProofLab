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

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ 


infixr ` ⟶ `:10 := precategory_str.hom -- type as \h
notation `𝟙` := precategory_str.id -- type as \b1
-- infixr ` ⊚ `:80 := precategory_str.comp-- type as \oo
local notation f ` ⊚ `:80 g:80 := precategory_str.comp g f    -- type as \oo

open PROOFS 
open PROOFS.STR


namespace category_str 


/-! ## Functors

Functors are homomorphism of categories, they are the way we map one category into another. 

A homomorphism `F : 𝓒 → 𝓓` maps 

- the objects of `𝓒` to the objects of `𝓓` (via a function `F₀ : 𝓒.obj → 𝓓.obj`)
- the morphisms of `𝓒` to the morphisms of `𝓓` (via a function `F₁ : 𝓒.mor → 𝓓.mor`)

in such a way that the operations of identity and compositions are preserved, i.e. 

- `F₁ (𝟙 X) = 𝟙 (F₀ X)` --  identities in `𝓒` go to identities in `𝓓` 
- `F₁ (g ⊚ f) = F₁(g) ⊚ F₁(f)` -- compositions in `𝓒` go to compositions in `𝓓` 
-/

set_option old_structure_cmd true


structure functor (𝓒 : Type u₁) [category_str.{v₁} 𝓒] (𝓓 : Type u₂) [category_str.{v₂} 𝓓] : Type (max v₁ v₂ u₁ u₂) :=
(obj [] : 𝓒 → 𝓓) -- the object function of functor structure
(mor : Π {X Y : 𝓒}, (X ⟶ Y) → (obj X ⟶ obj Y)) -- the morphism function of functor structure
(resp_id'   : 
∀ (X : 𝓒), mor (𝟙 X) = 𝟙 (obj X) )
(resp_comp' : 
∀ {X Y Z : 𝓒} (f : X ⟶ Y) (g : Y ⟶ Z), mor (g ⊚ f) = (mor g) ⊚  (mor f) )


#print functor

#check functor.obj -- the first function part of a  functor structure which maps objetcs to objects 
#check functor.mor --  the second function part of a  functor structure which maps morphisms to morphisms



section test 
variables {𝓒 𝓓 : Type} [category_str.{v₁} 𝓒] [category_str.{v₂} 𝓓]
variable F : functor 𝓒 𝓓 
#check F.obj  -- our informal notation for this was `F₀`
#check F.mor  -- our informal notation for this was `F₁`
variables {X Y Z : 𝓒}
variable g : X ⟶ Y 
variable f : Y ⟶ Z 
#check f ⊚ g
#check F.mor g -- F₁ g : F₀ X → F₀ Y
#check F.mor (f ⊚ g )
end test



infixr ` ⥤ `:26 := functor       -- type as \func --



restate_axiom functor.resp_id'
attribute [simp] functor.resp_id
restate_axiom functor.resp_comp'
attribute [simp] functor.resp_comp


namespace functor

#check @resp_id


variables {𝓒 : Type u₁} [category_str.{v₁} 𝓒]
          {𝓓  : Type u₂} [category_str.{v₂} 𝓓]
          {𝓔 : Type u₃} [category_str.{v₃} 𝓔]
          {𝓕 : Type u₄} [category_str.{v₄} 𝓕]
-- font MC stands for mathcal 𝓑 

-- a test that `attribute [simp] functor.resp_id'` works 
example (F : 𝓒 ⥤ 𝓓) (X : 𝓒) : F.mor (𝟙 X) = 𝟙 (F.obj X) :=
begin
  simp, 
end 

-- a test that `attribute [simp] functor.resp_comp'` works 
example (F : 𝓒 ⥤ 𝓓) {X Y Z : 𝓒} (f : X ⟶ Y) (g : Y ⟶ Z) : 
  F.mor (g ⊚ f ) = (F.mor g) ⊚ (F.mor f) :=
begin
  simp only [functor.resp_comp], 
end 


/- `𝟭 𝓒` is the identity functor on a category `𝓒`. -/
def id (𝓒 : Type u₁) [category_str.{v₁} 𝓒] : 𝓒 ⥤ 𝓒 :=
{
  obj := id, 
  mor := λ X, λ Y, λ f, f,
  resp_id' := by {intro X, refl, },
  resp_comp' := by {intros X Y Z, intro f, intro g, refl,} 
}

notation `𝟭` := functor.id -- Type this as `\sb1`


/- The identity function acts trivially on objects, i.e. it keeps them the same.-/
@[simp] 
lemma id_obj (X : 𝓒) : 
  (𝟭 𝓒).obj X = X := 
begin
  refl, 
end 


/- The identity function acts trivially on morphisms, i.e. it keeps them the same.-/
@[simp] 
lemma id_mor {X Y : 𝓒} (f : X ⟶ Y) : 
  (𝟭 𝓒).mor f = f :=
begin
  refl, 
end 

-- see how `simp` did it by uncommenting the line below:
--set_option trace.simplify.rewrite true


/- We can __compose__ functors. -/
def comp (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) : 𝓒 ⥤ 𝓔 :=
{
  obj := G.obj ∘ F.obj, 
  mor := λ X, λ Y, λ f, G.mor (F.mor f), 
  resp_id' := by {intro X, simp },
  resp_comp' := by {intros X Y Z f g, simp only [functor.resp_comp],},  
}

#check @functor.comp

local notation F ` ⊚⊚ `:80 G:80 := functor.comp G F 


@[simp]
lemma comp_id_obj (F : 𝓒 ⥤ 𝓓) (X : 𝓒) : 
  (F ⊚⊚ 𝟭 𝓒).obj X  = (F.obj X) :=
begin
  refl,
end 


@[simp]
lemma comp_id_mor (F : 𝓒 ⥤ 𝓓) {X Y : 𝓒} (f : X ⟶ Y) : 
  (F ⊚⊚ 𝟭 𝓒).mor f  = (F.mor f) :=
begin
  refl,
end 



@[simp]
lemma id_comp_obj (F : 𝓒 ⥤ 𝓓) (X : 𝓒) : 
  (𝟭 𝓓 ⊚⊚ F).obj X  = (F.obj X) :=
begin
  refl,
end


@[simp]
lemma id_comp_mor (F : 𝓒 ⥤ 𝓓) {X Y : 𝓒} (f : X ⟶ Y) : 
  (𝟭 𝓓 ⊚⊚ F).mor f  = (F.mor f) :=
begin
  refl,
end


lemma id_comp (F : 𝓒 ⥤ 𝓓) : 
  (𝟭 𝓓 ⊚⊚ F)  = F :=
begin
  sorry, 
end


lemma comp_id (F : 𝓒 ⥤ 𝓓) : 
  (F ⊚⊚ 𝟭 𝓒)  = F :=
begin
  sorry, 
end


@[simp]
lemma comp_assoc_obj (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) (H : 𝓔 ⥤ 𝓕) 
(X : 𝓒) : 
  ((H ⊚⊚ G) ⊚⊚ F).obj X = (H ⊚⊚ (G ⊚⊚ F)).obj X := 
begin 
  refl, 
end 


@[simp]
lemma comp_assoc_mor (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) (H : 𝓔 ⥤ 𝓕) (X Y: 𝓒) (f : X ⟶ Y): 
  ((H ⊚⊚ G) ⊚⊚ F).mor f = (H ⊚⊚ (G ⊚⊚ F)).mor f := 
begin 
  refl, 
end 




/-! ## Representable Functors  
To every object `X` of a category `𝓒` we can associate a functor `Ϳ X : 𝓒 ⥤ Type*` which maps an object `Y` in `𝓒` to the type `X ⟶ Y` of morphisms from `X` to `Y` in `𝓒`. 

Recall that To build a functor `F : 𝓒 ⥤ 𝓓` we need to specify four fields
* `obj : 𝓒 → 𝓓`
* `mor : ∀ {X Y : 𝓒} (f : X ⟶ Y), obj X ⟶ obj Y`
* `map_id'` and `map_comp'`, expressing the functor laws.
-/

--set_option trace.simp_lemmas true
@[simp]
def representable {𝓒 : Type*}[category_str 𝓒] (X : 𝓒) : 𝓒 ⥤ Type* :=
{ 
  obj := λ Y, X ⟶ Y,
  mor := λ Y Z f g, f ⊚ g,
  resp_id' := by {intro Y, funext, simp, refl, },
  resp_comp' := by {intros X Y Z f g, funext, simp, refl}, 
}

local notation ` Ϳ ` : 15 :=  functor.representable 


-- if `𝓒` is the cateogry of types, we have 
#check Ϳ ℕ 
#reduce (Ϳ ℕ).obj 
#reduce (Ϳ ℕ).obj ℤ 




@[simp]
def corepresentable {𝓒 : Type*}[category_str 𝓒] (X : 𝓒) : 𝓒ᵒᵖ ⥤ Type* :=
{ 
  obj := λ Y, unop Y ⟶ X, -- want 𝓒-morphisms from `Y` to `X`
  mor := λ Y Z f g, g ⊚ (hom.unop f),
  resp_id' := by {intro Y, funext, simp only [unop_id], simp, refl,  },
  resp_comp' := by {intros U' V' W' f g, simp only [unop_comp], funext x, rw ← comp_assoc, refl, },
}  


end functor




 


/- An example of bundling a type class with the base type is given by bundling the type class of `mult_monoid_str` which results in the type of monoids (i.e. types equipped with an instance of `mult_monoid_str`)-/

#check monoid

#check mult_monoid_str

structure mult_Monoid' := 
(carrier : Type)
(str : mult_monoid_str carrier )

#check mult_Monoid' -- this is the type of all monoids, i.e. a carrier type equipped with a s multiplicative monoid structure. 

/-
Similarly we can form the bundled type of all groups, rings, categories, etc. However, we like to have a uniform way of doing this, not only to save us the laborious work, but also introduced a general type class (`bundled` in below) which can be used for further instance synthesis and general coercions. 
-/





structure bundled (C : Type* → Type*) :=
(carrier : Type*)
(str : C carrier ) -- `C` is a type class specifying a structure. 

#check bundled


/-- A generic function for lifting a type equipped with an instance of a type class to an instance of a bundled type. -/

def bundled_of (C : Type* → Type*) (X : Type*) [str : C X] : bundled C := ⟨X, str⟩

#check bundled_of

#check nat.mult_monoid_str -- an instance of multiplicative monoid strucutre we defined in a previous lecture 

#check bundled_of mult_monoid_str ℕ -- Using ℕ and the instance `nat.mult_monoid_str` to define an instance of type `bundled mult_monoid_str`. 

variable {C : Type u₁ → Type v₁} 
-- forgetting the structure `C` and returning the carrier type. 
instance : has_coe_to_sort (bundled C) (Type*) := ⟨bundled.carrier⟩ -- an example would be to treat a group as its underlying type when needed. 


#check @bundled.mk -- Given a type class `C` and a `carrier X`, and an instance of `CX` the ouput is an instance of `bundled C`
#check @bundled.mk mult_monoid_str ℕ


@[simp] 
lemma coe_mk {C : Type u₁ → Type v₁} (carrier : Type u₁) (str) : 
  (@bundled.mk C carrier str : Type u₁) = carrier := 
begin
  refl,
end   




def mult_Monoid : Type* := bundled mult_monoid_str
def additive_Monoid := bundled additive_monoid_str
def additive_comm_Monoid := bundled comm_additive_monoid_str
def mult_Group : Type (u₁+1):= bundled mult_group_str
def additive_Group := bundled additive_group_str

/- Type of categories -/
def Cat := bundled small_category_str -- The type of small categories (where the types of morphims live in the universe `v`)


#check Cat

/- Examples of use of bundled types: 

If we have a term `M : mult_Monoid` ie a type bundled together with a monoid structure, then we can immediately infer that `M.str` is a monoid structure on the underlying type `M.carrier`. 
-/
instance (M : mult_Monoid) : mult_monoid_str M.carrier := M.str 
instance (G :additive_Group) : additive_group_str G.carrier := G.str 

#check bundled.str




/-! ## The Category of Monoids
Recall from HW10 how the idenity homomorphism of monoids and the compositions of homomorphisms of monoids were defined. 

Here we also prove the unitality and associativity of composition. 
-/

def mult_monoid.morphism.id {M : Type}[mult_monoid_str M] : M →ₘ* M := 
{
  to_fun := id, 
  resp_one := by {simp}, 
  resp_mul := by {simp},
}

@[simp]
def mult_monoid.morphism.comp {L M N : Type} [mult_monoid_str L] [mult_monoid_str M] [mult_monoid_str N] (g : M →ₘ* N) (f : L →ₘ* M) : L →ₘ* N := 
{ to_fun := g ∘ f,
  resp_one := by {simp},
  resp_mul := by {simp,}, } 


infixr  ` ∘* ` : 90  := mult_monoid.morphism.comp

local notation F ` ⊚⊚ `:80 G:80 := functor.comp G F 

@[simp]
lemma mult_monoid.morphism.id_comp {L M : Type} [mult_monoid_str L] [mult_monoid_str M]  (f : L →ₘ* M)  : 
  mult_monoid.morphism.id  ∘* f = f := 
begin 
  ext, 
  refl, 
end 


@[simp]
lemma mult_monoid.morphism.comp_id {L M : Type} [mult_monoid_str L] [mult_monoid_str M]  (f : L →ₘ* M)  : 
  f ∘* mult_monoid.morphism.id = f := 
begin 
  ext, 
  refl, 
end 


@[simp]
def mult_monoid.morphism.comp_assoc {K L M N: Type} [mult_monoid_str K] [mult_monoid_str L] [mult_monoid_str M] [mult_monoid_str N] (f : K →ₘ* L) (g : L →ₘ* M) (h : M →ₘ* N) : 
  (h ∘* g) ∘* f = h ∘* (g ∘* f) := 
begin 
  refl, 
end   


instance cat_of_monoids : large_category_str (mult_Monoid) := 
{ 
  hom := λ X Y, X.carrier →ₘ* Y.carrier, 
  id := λ X, mult_monoid.morphism.id,
  comp := λ X Y Z, λ f g, g ∘* f,
  id_comp' := by {intros X Y f, simp,},
  comp_id' := by {intros X Y f, simp,},
  comp_assoc' := by {intros X Y Z W f g h, apply  mult_monoid.morphism.comp_assoc}, 
}


#check large_category_str (mult_Monoid)

#check category_str.cat_of_monoids
#check category_str.cat_of_monoids.comp


/-
Challenge: do the same for groups. 
-/


#check mult_Monoid
#check functor



--set_option pp.instantiate_mvars false

--set_option trace.class_instances true
def forgetful_functor : mult_Monoid ⥤ mult_Monoid := 
sorry 

/-! ## The Category of categories and functors 
(Small) categories and functors between them form a (large) category. To show this, we first need to have a (larger) type of all categories and then introduce morphisms (i.e. functors) as part of the would-be structure of large category of categories. We do this by introducing a uniform way for bundling a type equipped with a type class. Examples below make this more clear. 
-/


#check Cat -- Type of small categories 

/- We want to endow `Cat` with the structure of category. -/

instance str (𝓒 : Cat) : small_category_str.{v₁} 𝓒.carrier := 𝓒.str

--instance : has_coe_to_sort Cat (Type u) := ⟨bundled.carrier⟩


--set_option trace.simplify.rewrite true
/-- Category structure on `Cat` -/
instance cat_of_cat : large_category_str Cat  :=
{ 
  hom := λ 𝓒 𝓓, 𝓒.carrier ⥤ 𝓓.carrier,
  id := λ 𝓒, 𝟭 𝓒.carrier,
  /- For composition after introducing `𝓒 𝓓 𝓔 F G` the context and goal are as follows

  𝓒 𝓓 𝓔 : Cat,
  F : ↥𝓒 ⥤ ↥𝓓,
  G : ↥𝓓 ⥤ ↥𝓔
  ⊢ ↥𝓒 ⥤ ↥𝓔
  
  Here `↥𝓒` is the underlying type of the category `𝓒`. 
  -/
  comp := λ 𝓒 𝓓 𝓔 F G, G ⊚⊚ F,  
  id_comp' := by {intros 𝓒 𝓓 F, apply functor.id_comp},
  comp_id' := by {intros 𝓒 𝓓 F, apply functor.id_comp, } 
 }

#check Cat ⥤ Cat 

#check Cat
#check category_str Cat 
#check category_str.cat_of_cat 


def delooping_cat (M : mult_Monoid) : Cat := 
⟨ (punit : Type u₁), category_str.delooping M.carrier⟩   

#check delooping_cat -- a function which sends a monoid to its deloopint category 



@[simp]
lemma deloop_type (M : mult_Monoid)  : 
  (delooping_cat M).carrier = (punit : Type u₁) := 
begin
  refl, 
end 


-- lemma deloop_mor (M : mult_Monoid) (X Y : (delooping_cat M).carrier) (m : X ⟶ Y) : (m : M.carrier) := 





#check delooping_cat 


#check category_str.delooping

/- Delooping is a functor `mult_Monoid ⥤ Cat` -/

#check functor


def delooping_functor : mult_Monoid ⥤ Cat := 
{ 
  obj := λ X, ⟨ punit, category_str.delooping X.carrier ⟩,
  mor := sorry,
  resp_id' := sorry,
  resp_comp' := sorry, 
}


end category_str 