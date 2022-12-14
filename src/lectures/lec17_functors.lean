/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# Morphisms of Categories: Functors
šŗ š š¼ šāā¬ šø š š š» š š¹
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import lectures.lec16_categories_basic



/-! ## Philosophical Remarks 
We mentioned that categories encompass many many mathematical structures. What is amazing is that categories, encompass categories too! Categories are themselves mathematical structures, and there is a good notion of "morphism between categories" which relates them. Such morphisms are called functors and they are very important in studying relating one field of mathematics to the other. For instance, in algebraic topology, we study spaces by their fundamental groups (or groupoids). ... 
-/

universes vā vā vā vā uā uā uā uā 


infixr ` ā¶ `:10 := precategory_str.hom -- type as \h
notation `š` := precategory_str.id -- type as \b1
-- infixr ` ā `:80 := precategory_str.comp-- type as \oo
local notation f ` ā `:80 g:80 := precategory_str.comp g f    -- type as \oo

open PROOFS 
open PROOFS.STR


namespace category_str 


/-! ## Functors

Functors are homomorphism of categories, they are the way we map one category into another. 

A homomorphism `F : š ā š` maps 

- the objects of `š` to the objects of `š` (via a function `Fā : š.obj ā š.obj`)
- the morphisms of `š` to the morphisms of `š` (via a function `Fā : š.mor ā š.mor`)

in such a way that the operations of identity and compositions are preserved, i.e. 

- `Fā (š X) = š (Fā X)` --  identities in `š` go to identities in `š` 
- `Fā (g ā f) = Fā(g) ā Fā(f)` -- compositions in `š` go to compositions in `š` 
-/

--set_option old_structure_cmd true

structure functor (š : Type uā) [category_str.{vā} š] (š : Type uā) [category_str.{vā} š] : Type (max vā vā uā uā) :=
(obj [] : š ā š) -- the object function of functor structure
(mor [] : Ī  {X Y : š}, (X ā¶ Y) ā (obj X ā¶ obj Y)) -- the morphism function of functor structure
(resp_id'   : 
ā (X : š), mor (š X) = š (obj X) )
(resp_comp' : 
ā {X Y Z : š} (f : X ā¶ Y) (g : Y ā¶ Z), mor (g ā f) = (mor g) ā  (mor f) )

-- attribute [class] functor
 
#print functor

#check functor.obj -- the first function part of a  functor structure which maps objetcs to objects 
#check functor.mor --  the second function part of a  functor structure which maps morphisms to morphisms



section test 
variables {š š : Type} [category_str.{vā} š] [category_str.{vā} š]
variable F : functor š š 
#check F.obj  -- our informal notation for this was `Fā`
#check F.mor  -- our informal notation for this was `Fā`
variables {X Y Z : š}
variable g : X ā¶ Y 
variable f : Y ā¶ Z 
#check f ā g
#check F.mor g -- Fā g : Fā X ā Fā Y
#check F.mor (f ā g )
end test



infixr ` ā„¤ `:26 := functor       -- type as \func --



restate_axiom functor.resp_id'
attribute [simp] functor.resp_id
restate_axiom functor.resp_comp'
attribute [simp] functor.resp_comp


namespace functor

#check @resp_id


variables {š : Type uā} [category_str.{vā} š]
          {š  : Type uā} [category_str.{vā} š]
          {š : Type uā} [category_str.{vā} š]
          {š : Type uā} [category_str.{vā} š]
-- font MC stands for mathcal š 

-- a test that `attribute [simp] functor.resp_id'` works 
example (F : š ā„¤ š) (X : š) : F.mor (š X) = š (F.obj X) :=
begin
  simp, 
end 

-- a test that `attribute [simp] functor.resp_comp'` works 
example (F : š ā„¤ š) {X Y Z : š} (f : X ā¶ Y) (g : Y ā¶ Z) : 
  F.mor (g ā f ) = (F.mor g) ā (F.mor f) :=
begin
  simp only [functor.resp_comp], 
end 


/- `š­ š` is the identity functor on a category `š`. -/
def id (š : Type uā) [category_str.{vā} š] : š ā„¤ š :=
{
  obj := id, 
  mor := Ī» X, Ī» Y, Ī» f, f,
  resp_id' := by {intro X, refl, },
  resp_comp' := by {intros X Y Z, intro f, intro g, refl,} 
}

notation `š­` := functor.id -- Type this as `\sb1`


/- The identity function acts trivially on objects, i.e. it keeps them the same.-/
@[simp] 
lemma id_obj (X : š) : 
  (š­ š).obj X = X := 
begin
  refl, 
end 


/- The identity function acts trivially on morphisms, i.e. it keeps them the same.-/
@[simp] 
lemma id_mor {X Y : š} (f : X ā¶ Y) : 
  (š­ š).mor f = f :=
begin
  refl, 
end 

-- see how `simp` did it by uncommenting the line below:
--set_option trace.simplify.rewrite true


/- We can __compose__ functors. -/
def comp (F : functor š š) (G : functor š š) : functor š š :=
{
  obj :=  Ī» X, G.obj (F.obj X), -- G.obj ā F.obj, 
  mor := Ī» X, Ī» Y, Ī» f, G.mor (F.mor f), 
  resp_id' := by {intro X, simp only [functor.resp_id ], },
  resp_comp' := by {intros X Y Z f g, simp only [functor.resp_comp],},  
}

-- /- We can __compose__ functors. -/
-- def comp (F : š ā„¤ š) (G : š ā„¤ š) : š ā„¤ š :=
-- {
--   obj :=  Ī» X, let t := (F.obj X) in G.obj t, -- G.obj ā F.obj, 
--   mor := Ī» X, Ī» Y, Ī» f, G.mor (F.mor f), 
--   resp_id' := by {intro X, simp },
--   resp_comp' := by {intros X Y Z f g, simp only [functor.resp_comp],},  
-- }

#check @functor.comp

local notation F ` āā `:80 G:80 := functor.comp G F 


@[simp]
lemma comp_id_obj (F : š ā„¤ š) (X : š) : 
  (F āā š­ š).obj X  = (F.obj X) :=
begin
  refl,
end 


@[simp]
lemma comp_id_mor (F : š ā„¤ š) {X Y : š} (f : X ā¶ Y) : 
  (F āā š­ š).mor f  = (F.mor f) :=
begin
  refl,
end 



@[simp]
lemma id_comp_obj (F : š ā„¤ š) (X : š) : 
  (š­ š āā F).obj X  = (F.obj X) :=
begin
  refl,
end


@[simp]
lemma id_comp_mor (F : š ā„¤ š) {X Y : š} (f : X ā¶ Y) : 
  (š­ š āā F).mor f  = (F.mor f) :=
begin
  refl,
end


lemma id_comp (F : š ā„¤ š) : 
  (š­ š āā F)  = F :=
begin
  sorry, 
end


lemma comp_id (F : š ā„¤ š) : 
  (F āā š­ š)  = F :=
begin
  sorry, 
end


@[simp]
lemma comp_assoc_obj (F : š ā„¤ š) (G : š ā„¤ š) (H : š ā„¤ š) 
(X : š) : 
  ((H āā G) āā F).obj X = (H āā (G āā F)).obj X := 
begin 
  refl, 
end 


@[simp]
lemma comp_assoc_mor (F : š ā„¤ š) (G : š ā„¤ š) (H : š ā„¤ š) (X Y: š) (f : X ā¶ Y): 
  ((H āā G) āā F).mor f = (H āā (G āā F)).mor f := 
begin 
  refl, 
end 




/-! ## Representable Functors  
To every object `X` of a category `š` we can associate a functor `Ķæ X : š ā„¤ Type*` which maps an object `Y` in `š` to the type `X ā¶ Y` of morphisms from `X` to `Y` in `š`. 

Recall that To build a functor `F : š ā„¤ š` we need to specify four fields
* `obj : š ā š`
* `mor : ā {X Y : š} (f : X ā¶ Y), obj X ā¶ obj Y`
* `map_id'` and `map_comp'`, expressing the functor laws.
-/

--set_option trace.simp_lemmas true
@[simp]
def representable {š : Type*}[category_str š] (X : š) : š ā„¤ Type* :=
{ 
  obj := Ī» Y, X ā¶ Y,
  mor := Ī» Y Z f g, f ā g,
  resp_id' := by {intro Y, funext, simp, refl, },
  resp_comp' := by {intros X Y Z f g, funext, simp, refl}, 
}

local notation ` Ķæ ` : 15 :=  functor.representable 


-- if `š` is the cateogry of types, we have 
#check Ķæ ā 
#reduce (Ķæ ā).obj 
#reduce (Ķæ ā).obj ā¤ 


#check š 
#check šįµįµ 
#check @category_str.opposite_cat šįµįµ 

@[simp]
def corepresentable {š : Type*}[category_str š] (X : š) : šįµįµ ā„¤ (Type*) :=
{ 
  obj := Ī» Y, unop Y ā¶ X, -- want š-morphisms from `Y` to `X`
  mor := Ī» Y Z f g, g ā (hom.unop f),
  resp_id' := by {intro Y, funext, simp only [unop_id], simp, refl,  },
  resp_comp' := by {intros U' V' W' f g, simp only [unop_comp], funext x, rw ā comp_assoc, refl, },
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





structure bundled (C : Type* ā Type*) :=
(carrier : Type*)
(str : C carrier ) -- `C` is a type class specifying a structure. 

#check bundled


/-- A generic function for lifting a type equipped with an instance of a type class to an instance of a bundled type. -/

def bundled_of (C : Type* ā Type*) (X : Type*) [str : C X] : bundled C := āØX, strā©

#check bundled_of

#check nat.mult_monoid_str -- an instance of multiplicative monoid strucutre we defined in a previous lecture 

#check bundled_of mult_monoid_str ā -- Using ā and the instance `nat.mult_monoid_str` to define an instance of type `bundled mult_monoid_str`. 

variable {C : Type uā ā Type vā} 
-- forgetting the structure `C` and returning the carrier type. 
instance : has_coe_to_sort (bundled C) (Type*) := āØbundled.carrierā© -- an example would be to treat a group as its underlying type when needed. 


#check @bundled.mk -- Given a type class `C` and a `carrier X`, and an instance of `CX` the ouput is an instance of `bundled C`
#check @bundled.mk mult_monoid_str ā


@[simp] 
lemma coe_mk {C : Type uā ā Type vā} (carrier : Type uā) (str) : 
  (@bundled.mk C carrier str : Type uā) = carrier := 
begin
  refl,
end   




def mult_Monoid : Type* := bundled mult_monoid_str
def additive_Monoid := bundled additive_monoid_str
def additive_comm_Monoid := bundled comm_additive_monoid_str
def mult_Group : Type (uā+1):= bundled mult_group_str
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

def mult_monoid.morphism.id {M : Type}[mult_monoid_str M] : M āā* M := 
{

  to_fun := id, 
  resp_one := by {simp}, 
  resp_mul := by {simp},
}

@[simp]
def mult_monoid.morphism.comp {L M N : Type} [mult_monoid_str L] [mult_monoid_str M] [mult_monoid_str N] (g : M āā* N) (f : L āā* M) : L āā* N := 
{ to_fun := g ā f,
  resp_one := by {simp},
  resp_mul := by {simp,}, } 


infixr  ` ā* ` : 90  := mult_monoid.morphism.comp

local notation F ` āā `:80 G:80 := functor.comp G F 

@[simp]
lemma mult_monoid.morphism.id_comp {L M : Type} [mult_monoid_str L] [mult_monoid_str M]  (f : L āā* M)  : 
  mult_monoid.morphism.id  ā* f = f := 
begin 
  ext, 
  refl, 
end 


@[simp]
lemma mult_monoid.morphism.comp_id {L M : Type} [mult_monoid_str L] [mult_monoid_str M]  (f : L āā* M)  : 
  f ā* mult_monoid.morphism.id = f := 
begin 
  ext, 
  refl, 
end 


@[simp]
def mult_monoid.morphism.comp_assoc {K L M N: Type} [mult_monoid_str K] [mult_monoid_str L] [mult_monoid_str M] [mult_monoid_str N] (f : K āā* L) (g : L āā* M) (h : M āā* N) : 
  (h ā* g) ā* f = h ā* (g ā* f) := 
begin 
  refl, 
end   


instance cat_of_monoids : large_category_str (mult_Monoid) := 
{ 
  hom := Ī» X Y, X.carrier āā* Y.carrier, 
  id := Ī» X, mult_monoid.morphism.id,
  comp := Ī» X Y Z, Ī» f g, g ā* f,
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
def forgetful_functor : mult_Monoid ā„¤ mult_Monoid := 
sorry 

/-! ## The Category of categories and functors 
(Small) categories and functors between them form a (large) category. To show this, we first need to have a (larger) type of all categories and then introduce morphisms (i.e. functors) as part of the would-be structure of large category of categories. We do this by introducing a uniform way for bundling a type equipped with a type class. Examples below make this more clear. 
-/


#check Cat -- Type of small categories 

/- We want to endow `Cat` with the structure of category. -/

instance str (š : Cat) : small_category_str.{vā} š.carrier := š.str

--instance : has_coe_to_sort Cat (Type u) := āØbundled.carrierā©


--set_option trace.simplify.rewrite true
/-- Category structure on `Cat` -/
instance cat_of_cat : large_category_str Cat  :=
{ 
  hom := Ī» š š, š.carrier ā„¤ š.carrier,
  id := Ī» š, š­ š.carrier,
  /- For composition after introducing `š š š F G` the context and goal are as follows

  š š š : Cat,
  F : ā„š ā„¤ ā„š,
  G : ā„š ā„¤ ā„š
  ā¢ ā„š ā„¤ ā„š
  
  Here `ā„š` is the underlying type of the category `š`. 
  -/
  comp := Ī» š š š F G, G āā F,  
  id_comp' := by {intros š š F, apply functor.id_comp},
  comp_id' := by {intros š š F, apply functor.id_comp, } 
 }

#check Cat ā„¤ Cat 

#check Cat
#check category_str Cat 
#check category_str.cat_of_cat 


def delooping_cat (M : mult_Monoid) : Cat := 
āØ (punit : Type uā), category_str.delooping M.carrierā©   

#check delooping_cat -- a function which sends a monoid to its deloopint category 



@[simp]
lemma deloop_type (M : mult_Monoid)  : 
  (delooping_cat M).carrier = (punit : Type uā) := 
begin
  refl, 
end 


-- lemma deloop_mor (M : mult_Monoid) (X Y : (delooping_cat M).carrier) (m : X ā¶ Y) : (m : M.carrier) := 





#check delooping_cat 


#check category_str.delooping

/- Delooping is a functor `mult_Monoid ā„¤ Cat` -/

#check functor


def delooping_functor : mult_Monoid ā„¤ Cat := 
{ 
  obj := Ī» X, āØ punit, category_str.delooping X.carrier ā©,
  mor := sorry,
  resp_id' := sorry,
  resp_comp' := sorry, 
}


end category_str 