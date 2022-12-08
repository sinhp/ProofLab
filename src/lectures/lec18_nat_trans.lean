/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# Morphisms of Functors: Natural Transformations
😺 🐈 😼 🐈‍⬛ 😸 🐈 🙀 😻 🐈 😹
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import lectures.lec17_functors
import tactic.basic

open category_str


/-!
## Natural transformations

Consider the collection of functors from category `𝓒` to category `𝓓`. This collection is prima facie a type. But we shall give it the structure of a category whose objects are functors `𝓒 → 𝓓` and whose morphisms are what we call __natural transformations__ between functors. To talk about the natural transformations, we just write `F ⟶ G` using the usual "morphism" arrow.

So, what is a naturan transformation?

A __natural transformation__ `α : nat_trans F G` consists of morphisms `α.app X : F.obj X ⟶ G.obj X`,
and the naturality squares `α.naturality f : F.map f ≫ α.app Y = α.app X ≫ G.map f`, where `f : X ⟶ Y`.

F.obj X ---> F.obj Y
  |             |
  |             |
  |             |
  v             v
G.obj X ---> G.obj Y 

or even more informally, 

F X ----> F Y 
 |         |              
 |         |        
 v         v                
G X ----> G Y 

-/

--infixr ` ⟶ `:10 := precategory_str.hom -- type as \h
--notation `𝟙` := precategory_str.id -- type as \b1
-- infixr ` ⊚ `:80 := precategory_str.comp-- type as \oo
local notation f ` ⊚ `:80 g:80 := precategory_str.comp g f    -- type as \oo



universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {𝓒 : Type u₁} [category_str.{v₁} 𝓒] {𝓓 : Type u₂} [category_str.{v₂} 𝓓]


@[ext]
structure nat_trans (F G : 𝓒 ⥤ 𝓓) : Type (max u₁ v₂) :=
(cmpt : Π X : 𝓒, F.obj X ⟶ G.obj X) -- "cmp" short for "component"
(naturality' : ∀ ⦃X Y : 𝓒⦄ (f : X ⟶ Y), cmpt Y ⊚ (F.mor f) = (G.mor f)  ⊚ cmpt X . obviously) -- the naturality condition which says the square above commutes

#check nat_trans
#check @nat_trans

#check nat_trans.cmpt

restate_axiom nat_trans.naturality'

/-
Note that we make `nat_trans.naturality` a simp lemma, with the preferred simp normal form pushing components of natural transformations to the left.
-/ 

attribute [simp] nat_trans.naturality





section test --testing our definition and notation 
variables 
variables F G : 𝓒 ⥤ 𝓓 -- `F` and `G` are functors 
#check F.obj  -- our informal notation for this was `F₀`
#check F.mor  -- our informal notation for this was `F₁`

variables {X Y Z : 𝓒}
variable f : X ⟶ Y 
variable g : Y ⟶ Z 


#check (F.mor f : F.obj X ⟶ F.obj Y) 
#check  (G.mor f : G.obj X ⟶ G.obj Y) 


variable θ : nat_trans F G 

#check (θ.cmpt : Π (X : 𝓒), F.obj X ⟶ G.obj X)

#check (θ.cmpt X : F.obj X ⟶ G.obj X) --the component of natural transformation `θ` at object `X` . If `θ : F ⟶ G`, then `θ.cmpt X` is the component at `X`, i.e. a morphism `F.obj X ⟶ G.obj X`.

#check (θ.cmpt Y : F.obj Y ⟶ G.obj Y) --the component of natural transformation `θ` at object `Y`,

#check θ.naturality

/-              F.mor f
          F X ---------> F Y 
          |               |              
 θ.cmpt X |               | θ.cmpt Y       
          v               v                
          G X ---------> G Y 
                 G.mor f
-/                 

example : 
  (θ.cmpt Y) ⊚ (F.mor f) = (G.mor f) ⊚ (θ.cmpt X) := 
begin
  rw [θ.naturality], 
end   

end test




namespace nat_trans


/- Let's prove that if two natural transforamtions are equal then all of their components are equal. -/

lemma congr_cmpt {F G : 𝓒 ⥤ 𝓓} {α β : nat_trans F G} (h : α = β) (X : 𝓒) : 
  α.cmpt X = β.cmpt X :=
begin
 have h₁ :  α.cmpt = β.cmpt , from congr_arg nat_trans.cmpt h, 
 apply congr_fun h₁, 
end 


/- The __identity__ natural transformation on a functor `
`F`. -/ 

def id (F : 𝓒 ⥤ 𝓓) : nat_trans F F :=
{ 
  cmpt := λ X, 𝟙 (F.obj X), 
  naturality' := by {
                      intros X Y f,
                      simp only [id_comp, comp_id],
                    },  
}


#check nat_trans.id


@[simp] 
lemma id_cmpt {F: 𝓒 ⥤ 𝓓} (X : 𝓒) : 
  (nat_trans.id F).cmpt X = 𝟙 (F.obj X) := 
begin
  refl, 
end 




/-! ## Composition of Natural Transformations 

Natural transformations have two kinds of compositions: 

1. The vertical composition, and 
2. The horizontal composition

The vertical composition is easier to describe, so we start from that. 
-/



/-! ### Vertical Composition of Natural Transformations 

Given functors `F G : 𝓒 ⥤ 𝓓` and natural transformations 
`α : nat_trans F G ` and  `β : nat_trans G H`, for any object `X` in category `𝓒` we obtain the comutative diagram 

F X ----> F Y 
 |         |              
 |         |        
 v         v                
G X ----> G Y 
 |         |
 |         |   
 v         v
H X ----> H Y 

The vertical composition of `α` and `β` has at its `X` components the composite morphism `(β.cmpt X) ⊚ (α.cmpt X)`.   
-/

/-- `vcomp α β` is the __vertical__ compositions of natural transformations. -/

variables {F G H : 𝓒 ⥤ 𝓓}


-- def vcomp (α : nat_trans F G) (β : nat_trans G H) : nat_trans F H :=
-- { cmpt := λ X, (β.cmpt X) ⊚ (α.cmpt X), -- composition of morphisms in 𝓓
--   naturality' := by {intros X Y f, simp, } }













@[simp]
def vcomp (α : nat_trans F G) (β : nat_trans G H) : nat_trans F H :=
{ 
  cmpt := λ X, (β.cmpt X) ⊚ (α.cmpt X), 
  naturality' := by { intros X Y f, 
                      rw category_str.comp_assoc,
                      simp only [α.naturality], 
                      rw ← category_str.comp_assoc, 
                      simp only [β.naturality], 
                      rw category_str.comp_assoc,
                      } ,
}


#check vcomp 



--@[simp]
lemma vcomp_cmpt (α : nat_trans F G) (β : nat_trans G H) (X : 𝓒) :
  (vcomp α β).cmpt X = (β.cmpt X) ⊚ (α.cmpt X)  := 
begin
  refl,
end   




/- Challenge: prove that that the naturality square of `g ⊚ f` is derived from the naturality square of `f` and `g`.  

   F(f)      F(g)      
F X ----> F Y ----> F Z
 |         |         |         
 | α(X)    | α(Y)    | α(U)    
 v         v         v         
G X ----> G Y ----> G Z
    G(f)      G(g)      
-/




/-
As a simple exercise let's prove that if we vertically compose any natural transformation `θ` with `nat_trans.id`, we get `θ`. 
-/








/-
- Functions are the way we map one type into another.  
For types `X Y : Type` we have the type `X → Y` of functions from `X` to `Y` 

- Functors are the way we map one category into another.  
For categories `𝓒 𝓓` we construct a category structures on functors `𝓒 ⥤ 𝓓`. We call this the __functor category__ of `𝓒` and `𝓓`. 

`functor_cat 𝓒 𝓓` gives the category structure on functors and natural transformations
between categories `𝓒` and `D`.

Notice that if `𝓒` and `𝓓` are both small categories at the same universe level, this is another small category at that level.

However if `𝓒` and `𝓓` are both large categories at the same universe level,
this is a small category at the next higher level.
-/


#check 𝓒 ⥤ 𝓓 

instance functor.cat : category_str.{(max u₁ v₂)} (𝓒 ⥤ 𝓓) :=
{ 
  hom     := λ F G, nat_trans F G,
  id      := λ F, nat_trans.id F,
  comp    := λ _ _ _ α β, vcomp α β, 
  id_comp' := by {intros F G θ, ext, simp, },  
  comp_id' := by {intros F G θ, ext, simp,}, 
  comp_assoc' := by {intros F G H K α β γ, ext, simp only [vcomp_cmpt], rw [comp_assoc], },
}


/-
Take a functor `F : 𝓒 ⥤ 𝓓`. This is an object of the functor category `𝓒 ⥤ 𝓓`. Therefore, we have an idenity morphism `𝟙 F : F ⟶ F` in the functors category `𝓒 ⥤ 𝓓`. This is the identity natural transformation.
-/

--@[simp] 
lemma functor.cat.id_eq_id_trans : 
  (𝟙 F : F ⟶ F) = nat_trans.id F := 
begin
  refl, 
end   


@[simp] 
lemma functor.cat.vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : 
  vcomp α β =  β  ⊚ α := 
begin
  refl,  -- by definition of `vcomp` and the category structure on 𝓒 ⥤ 𝓓 
end 



@[simp] 
lemma functor.cat.id_cmpt (F : 𝓒 ⥤ 𝓓) (X : 𝓒) : 
  (𝟙 F : F ⟶ F).cmpt X = 𝟙 (F.obj X) := rfl


@[simp] lemma functor.cat.comp_cmpt {F G H : 𝓒 ⥤ 𝓓} (α : F ⟶ G) (β : G ⟶ H) (X : 𝓒) :
  (β ⊚ α).cmpt X = β.cmpt X ⊚ α.cmpt X :=  
  --these two compositions happen in different categories. Can you guess where?
begin
  refl, -- by definition 
end 


#check functor.representable 




local notation ` 𝓙 ` : 15 :=  functor.representable 
local notation ` c𝓙 ` : 15 :=  functor.corepresentable 



@[simp]
lemma corep_obj (X : 𝓒) (Y : 𝓒ᵒᵖ) :  
  (c𝓙 X).obj Y =  (unop Y ⟶ X) := 
begin
  refl, 
end 


@[simp]
lemma corep_mor (X : 𝓒) (Y Z : 𝓒ᵒᵖ) (f : Y ⟶ Z) :  
   (c𝓙 X).mor f =  λ g, g ⊚ (hom.unop f) := 
begin
  refl, 
end 




def ℍom : 𝓒 ⥤ (𝓒ᵒᵖ ⥤ Type v₁) :=
{ 
  -- the action of ℍom on objects of 𝓒
  obj := λ X, c𝓙 X, 
  -- the action of ℍom on morphisms of 𝓒
  mor := λ X Y, λ f, { cmpt := λ W, λ g, f ⊚ g,
                       naturality' := 
                       by { 
                             intros U V k, 
                             dsimp, 
                             funext x, 
                             change f ⊚ (x ⊚ (hom.unop k)) = (f ⊚ x) ⊚ (hom.unop k), 
                             simp only [comp_assoc], 
                          },
                      },
  -- ℍom is functorial, it respects identities and compositions in 𝓒.                     
  resp_id' := by {intro X, ext Y, simp, refl, },
  resp_comp' := by {
                      intros X Y Z f g, 
                      ext U, 
                      simp, 
                      refl,  
                    }, 
  }



def Yoneda (X Y : 𝓒) (α : ℍom.obj X ≅  ℍom.obj Y) : 
  X ≅ Y :=
{ 
  to_mor := α.to_mor.cmpt (op X) (𝟙 X),
  inv_mor := α.inv_mor.cmpt (op Y) (𝟙 Y),
  left_inv := sorry,
  right_inv := sorry, 
}





-- def Yoneda (X Y : 𝓒) (α : ℍom.obj X ≅  ℍom.obj Y) : 
--   X ≅ Y :=
-- { 
--   to_mor := α.to_mor.cmpt (op X) (𝟙 X),
--   inv_mor := α.inv_mor.cmpt (op Y) (𝟙 Y),
--   left_inv := by { have h₁, from α.inv_mor.naturality (α.to_mor.cmpt (op X) (𝟙 X)), simp at h₁,  
--   },
--   right_inv := sorry, 
-- }





end nat_trans

















