/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# Morphisms of Functors: Natural Transformations
šŗ š š¼ šāā¬ šø š š š» š š¹
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import lectures.lec17_functors
import tactic.basic

open category_str


/-!
## Natural transformations

Consider the collection of functors from category `š` to category `š`. This collection is prima facie a type. But we shall give it the structure of a category whose objects are functors `š ā š` and whose morphisms are what we call __natural transformations__ between functors. To talk about the natural transformations, we just write `F ā¶ G` using the usual "morphism" arrow.

So, what is a naturan transformation?

A __natural transformation__ `Ī± : nat_trans F G` consists of morphisms `Ī±.app X : F.obj X ā¶ G.obj X`,
and the naturality squares `Ī±.naturality f : F.map f ā« Ī±.app Y = Ī±.app X ā« G.map f`, where `f : X ā¶ Y`.

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

--infixr ` ā¶ `:10 := precategory_str.hom -- type as \h
--notation `š` := precategory_str.id -- type as \b1
-- infixr ` ā `:80 := precategory_str.comp-- type as \oo
local notation f ` ā `:80 g:80 := precategory_str.comp g f    -- type as \oo



universes vā vā vā vā uā uā uā uā

variables {š : Type uā} [category_str.{vā} š] {š : Type uā} [category_str.{vā} š]


@[ext]
structure nat_trans (F G : š ā„¤ š) : Type (max uā vā) :=
(cmpt : Ī  X : š, F.obj X ā¶ G.obj X) -- "cmp" short for "component"
(naturality' : ā ā¦X Y : šā¦ (f : X ā¶ Y), cmpt Y ā (F.mor f) = (G.mor f)  ā cmpt X . obviously) -- the naturality condition which says the square above commutes

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
variables F G : š ā„¤ š -- `F` and `G` are functors 
#check F.obj  -- our informal notation for this was `Fā`
#check F.mor  -- our informal notation for this was `Fā`

variables {X Y Z : š}
variable f : X ā¶ Y 
variable g : Y ā¶ Z 


#check (F.mor f : F.obj X ā¶ F.obj Y) 
#check  (G.mor f : G.obj X ā¶ G.obj Y) 


variable Īø : nat_trans F G 

#check (Īø.cmpt : Ī  (X : š), F.obj X ā¶ G.obj X)

#check (Īø.cmpt X : F.obj X ā¶ G.obj X) --the component of natural transformation `Īø` at object `X` . If `Īø : F ā¶ G`, then `Īø.cmpt X` is the component at `X`, i.e. a morphism `F.obj X ā¶ G.obj X`.

#check (Īø.cmpt Y : F.obj Y ā¶ G.obj Y) --the component of natural transformation `Īø` at object `Y`,

#check Īø.naturality

/-              F.mor f
          F X ---------> F Y 
          |               |              
 Īø.cmpt X |               | Īø.cmpt Y       
          v               v                
          G X ---------> G Y 
                 G.mor f
-/                 

example : 
  (Īø.cmpt Y) ā (F.mor f) = (G.mor f) ā (Īø.cmpt X) := 
begin
  rw [Īø.naturality], 
end   

end test




namespace nat_trans


/- Let's prove that if two natural transforamtions are equal then all of their components are equal. -/

lemma congr_cmpt {F G : š ā„¤ š} {Ī± Ī² : nat_trans F G} (h : Ī± = Ī²) (X : š) : 
  Ī±.cmpt X = Ī².cmpt X :=
begin
 have hā :  Ī±.cmpt = Ī².cmpt , from congr_arg nat_trans.cmpt h, 
 apply congr_fun hā, 
end 


/- The __identity__ natural transformation on a functor `
`F`. -/ 

def id (F : š ā„¤ š) : nat_trans F F :=
{ 
  cmpt := Ī» X, š (F.obj X), 
  naturality' := by {
                      intros X Y f,
                      simp only [id_comp, comp_id],
                    },  
}


#check nat_trans.id


@[simp] 
lemma id_cmpt {F: š ā„¤ š} (X : š) : 
  (nat_trans.id F).cmpt X = š (F.obj X) := 
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

Given functors `F G : š ā„¤ š` and natural transformations 
`Ī± : nat_trans F G ` and  `Ī² : nat_trans G H`, for any object `X` in category `š` we obtain the comutative diagram 

F X ----> F Y 
 |         |              
 |         |        
 v         v                
G X ----> G Y 
 |         |
 |         |   
 v         v
H X ----> H Y 

The vertical composition of `Ī±` and `Ī²` has at its `X` components the composite morphism `(Ī².cmpt X) ā (Ī±.cmpt X)`.   
-/

/-- `vcomp Ī± Ī²` is the __vertical__ compositions of natural transformations. -/

variables {F G H : š ā„¤ š}


-- def vcomp (Ī± : nat_trans F G) (Ī² : nat_trans G H) : nat_trans F H :=
-- { cmpt := Ī» X, (Ī².cmpt X) ā (Ī±.cmpt X), -- composition of morphisms in š
--   naturality' := by {intros X Y f, simp, } }













@[simp]
def vcomp (Ī± : nat_trans F G) (Ī² : nat_trans G H) : nat_trans F H :=
{ 
  cmpt := Ī» X, (Ī².cmpt X) ā (Ī±.cmpt X), 
  naturality' := by { intros X Y f, 
                      rw category_str.comp_assoc,
                      simp only [Ī±.naturality], 
                      rw ā category_str.comp_assoc, 
                      simp only [Ī².naturality], 
                      rw category_str.comp_assoc,
                      } ,
}


#check vcomp 



--@[simp]
lemma vcomp_cmpt (Ī± : nat_trans F G) (Ī² : nat_trans G H) (X : š) :
  (vcomp Ī± Ī²).cmpt X = (Ī².cmpt X) ā (Ī±.cmpt X)  := 
begin
  refl,
end   




/- Challenge: prove that that the naturality square of `g ā f` is derived from the naturality square of `f` and `g`.  

   F(f)      F(g)      
F X ----> F Y ----> F Z
 |         |         |         
 | Ī±(X)    | Ī±(Y)    | Ī±(U)    
 v         v         v         
G X ----> G Y ----> G Z
    G(f)      G(g)      
-/




/-
As a simple exercise let's prove that if we vertically compose any natural transformation `Īø` with `nat_trans.id`, we get `Īø`. 
-/








/-
- Functions are the way we map one type into another.  
For types `X Y : Type` we have the type `X ā Y` of functions from `X` to `Y` 

- Functors are the way we map one category into another.  
For categories `š š` we construct a category structures on functors `š ā„¤ š`. We call this the __functor category__ of `š` and `š`. 

`functor_cat š š` gives the category structure on functors and natural transformations
between categories `š` and `D`.

Notice that if `š` and `š` are both small categories at the same universe level, this is another small category at that level.

However if `š` and `š` are both large categories at the same universe level,
this is a small category at the next higher level.
-/


#check š ā„¤ š 

instance functor.cat : category_str.{(max uā vā)} (š ā„¤ š) :=
{ 
  hom     := Ī» F G, nat_trans F G,
  id      := Ī» F, nat_trans.id F,
  comp    := Ī» _ _ _ Ī± Ī², vcomp Ī± Ī², 
  id_comp' := by {intros F G Īø, ext, simp, },  
  comp_id' := by {intros F G Īø, ext, simp,}, 
  comp_assoc' := by {intros F G H K Ī± Ī² Ī³, ext, simp only [vcomp_cmpt], rw [comp_assoc], },
}


/-
Take a functor `F : š ā„¤ š`. This is an object of the functor category `š ā„¤ š`. Therefore, we have an idenity morphism `š F : F ā¶ F` in the functors category `š ā„¤ š`. This is the identity natural transformation.
-/

--@[simp] 
lemma functor.cat.id_eq_id_trans : 
  (š F : F ā¶ F) = nat_trans.id F := 
begin
  refl, 
end   


@[simp] 
lemma functor.cat.vcomp_eq_comp (Ī± : F ā¶ G) (Ī² : G ā¶ H) : 
  vcomp Ī± Ī² =  Ī²  ā Ī± := 
begin
  refl,  -- by definition of `vcomp` and the category structure on š ā„¤ š 
end 



@[simp] 
lemma functor.cat.id_cmpt (F : š ā„¤ š) (X : š) : 
  (š F : F ā¶ F).cmpt X = š (F.obj X) := rfl


@[simp] lemma functor.cat.comp_cmpt {F G H : š ā„¤ š} (Ī± : F ā¶ G) (Ī² : G ā¶ H) (X : š) :
  (Ī² ā Ī±).cmpt X = Ī².cmpt X ā Ī±.cmpt X :=  
  --these two compositions happen in different categories. Can you guess where?
begin
  refl, -- by definition 
end 


#check functor.representable 




local notation ` š ` : 15 :=  functor.representable 
local notation ` cš ` : 15 :=  functor.corepresentable 



@[simp]
lemma corep_obj (X : š) (Y : šįµįµ) :  
  (cš X).obj Y =  (unop Y ā¶ X) := 
begin
  refl, 
end 


@[simp]
lemma corep_mor (X : š) (Y Z : šįµįµ) (f : Y ā¶ Z) :  
   (cš X).mor f =  Ī» g, g ā (hom.unop f) := 
begin
  refl, 
end 




def āom : š ā„¤ (šįµįµ ā„¤ Type vā) :=
{ 
  -- the action of āom on objects of š
  obj := Ī» X, cš X, 
  -- the action of āom on morphisms of š
  mor := Ī» X Y, Ī» f, { cmpt := Ī» W, Ī» g, f ā g,
                       naturality' := 
                       by { 
                             intros U V k, 
                             dsimp, 
                             funext x, 
                             change f ā (x ā (hom.unop k)) = (f ā x) ā (hom.unop k), 
                             simp only [comp_assoc], 
                          },
                      },
  -- āom is functorial, it respects identities and compositions in š.                     
  resp_id' := by {intro X, ext Y, simp, refl, },
  resp_comp' := by {
                      intros X Y Z f g, 
                      ext U, 
                      simp, 
                      refl,  
                    }, 
  }



def Yoneda (X Y : š) (Ī± : āom.obj X ā  āom.obj Y) : 
  X ā Y :=
{ 
  to_mor := Ī±.to_mor.cmpt (op X) (š X),
  inv_mor := Ī±.inv_mor.cmpt (op Y) (š Y),
  left_inv := sorry,
  right_inv := sorry, 
}





-- def Yoneda (X Y : š) (Ī± : āom.obj X ā  āom.obj Y) : 
--   X ā Y :=
-- { 
--   to_mor := Ī±.to_mor.cmpt (op X) (š X),
--   inv_mor := Ī±.inv_mor.cmpt (op Y) (š Y),
--   left_inv := by { have hā, from Ī±.inv_mor.naturality (Ī±.to_mor.cmpt (op X) (š X)), simp at hā,  
--   },
--   right_inv := sorry, 
-- }





end nat_trans

















