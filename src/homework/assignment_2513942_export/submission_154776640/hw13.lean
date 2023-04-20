/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# HW 13 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import lectures.lec18_nat_trans
import tactic.basic

open PROOFS
open PROOFS.STR


open category_str

--infixr ` ⟶ `:10 := precategory_str.hom -- type as \h
--notation `𝟙` := precategory_str.id -- type as \b1
-- infixr ` ⊚ `:80 := precategory_str.comp-- type as \oo
local notation f ` ⊚ `:80 g:80 := precategory_str.comp g f 

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ 
variables {𝓒 : Type u₁} [category_str.{v₁} 𝓒] {𝓓 : Type u₂} [category_str.{v₂} 𝓓]

/-! ## Q1. Construct the type of all groups. 
Show that this type admits the structure of a (large) category where 
morphisms are group homomorphisms.-/

structure mult_Group' := 
(carrier : Type)
(str : mult_group_str carrier )

#check mult_Group' -- type of all groups, carrier type equipped with a multiplicative group strucutre 

structure bundled (C : Type v₁ → Type u₁) :=
(carrier : Type*)
(str : C carrier )

instance (M : mult_Group') : mult_group_str M.carrier := M.str 


-- OUR GOAL IS FIRST TO DEFINE A CATEGORY WHERE MORPHISMS ARE GROUP HOMOMORPHISMS

@[ext] -- first we define a class of morphisms between group structures
--  A group morphism between groups `M` and `N` is given by a function `f : M → N` which preserves the multiplication operation.
class mult_Group.morphism (M : Type u₁) (N : Type u₁) [mult_group_str M] [mult_group_str N] :=
(to_fun : M → N) -- f : M → N -- the underlying function of morphism
(resp_one : to_fun 1 = 1) -- f (1_M ) = 1_N
(resp_mul : ∀ x y : M, to_fun (x * y) = to_fun x * to_fun y)

#check mult_Group.morphism

-- first we defined an identity morphism between group structures 
def mult_group.morphism.id {M : Type}[mult_group_str M] : mult_Group.morphism M M:= 
{
  to_fun := id, -- in order to define an identity function, we provide id 
  resp_one := by { -- our goal is to prove `id 1 = 1` 
    refl, -- By defintion `id 1` and `1` are equal 
    }, 
  resp_mul := by { -- our goal is to prove `∀ (x y : M), id ( x * y) = id x * id y` 
  intros x y, -- First, we fix ` x y : M ` in the context 
  simp,}, -- since ` id x = x ` by defintion, ` id y = y ` by defintion, and ` id ( x * y ) = x * y `  by defintion, the goal can be written as ` x * y = x * y ` which is resolved since both sides are defintionally equal 
}

-- next we must define composition of group morphisms 
@[simp]
def mult_Group.morphism.comp {L M N : Type} [mult_group_str L] [mult_group_str M] [mult_group_str N] (g : mult_Group.morphism M N) (f : mult_Group.morphism L M) : mult_Group.morphism L N := 
{ to_fun := g.to_fun ∘ f.to_fun, -- composotion of group morphisms is defined as the composition of the to_fun component of each group morphism
  resp_one := by { -- our goal is to prove `(morphism.to_fun ∘ morphism.to_fun) 1 = 1` 
  dsimp, -- through simplification, the composition is simplified so that the goal turns into ` morphism.to_fun (morphism.to_fun 1) = 1`
  rw mult_Group.morphism.resp_one, -- our goal is to resolve `morphism.to_fun (morphism.to_fun 1) = 1` and there exists a mult_Group.morphism on g and f, a property of this morphism is that it respects one, therefore this property can be invoked 
  rw mult_Group.morphism.resp_one,}, -- our goal is to resolve ` morphism.to_fun 1 = 1 ` and since there exists a mult_Group.morphism on g and f, this resolves a property of this morphsim which resolves the goal 
  resp_mul := by { -- our goal is to prove `∀ (x y : L), (morphism.to_fun ∘ morphism.to_fun) (x * y) = (morphism.to_fun ∘ morphism.to_fun) x * (morphism.to_fun ∘ morphism.to_fun) y`
  intros x y, -- we fix ` x y : L ` in the context 
  dsimp, -- through simplification, the composition is simplified so that the goal turns into `morphism.to_fun (morphism.to_fun (x * y)) = morphism.to_fun (morphism.to_fun x) * morphism.to_fun (morphism.to_fun y`
  rw mult_Group.morphism.resp_mul, -- our goal is to resolve `morphism.to_fun (morphism.to_fun (x * y)) = morphism.to_fun (morphism.to_fun x) * morphism.to_fun (morphism.to_fun y` and since there exists a mult_Group.morphism on g and f, this resolves a property of this morphsim which resolves the goal 
  rw mult_Group.morphism.resp_mul, }, -- our goalis to resolve ` morphism.to_fun (morphism.to_fun x * morphism.to_fun y) = morphism.to_fun (morphism.to_fun x) * morphism.to_fun (morphism.to_fun y` and since there exists a mult_Group.morphism on g and f, this resolves a property of this morphsim which resolves the goal 
} 

-- in order to admit a category whose morphisms are group morphisms, we create lemmas which satifisy the fields of a category_str
@[simp]
lemma mult_group.morphism.id_comp {L M : Type} [mult_group_str L] [mult_group_str M]  (f : mult_Group.morphism L M)  : 
  mult_Group.morphism.comp f (mult_group.morphism.id) = f := 
begin 3
  ext, -- By extensionality, it is sufficient to prove the to_fun components of the morphism f and id when composed yields the original to_fun function
  refl, -- Our goal is transformed to `morphism.to_fun x = morphism.to_fun x` and both sides are definitionally equal 
end 

@[simp]
lemma mult_group.morphism.comp_id {L M : Type} [mult_group_str L] [mult_group_str M]  (f : mult_Group.morphism L M)  : 
  mult_Group.morphism.comp (mult_group.morphism.id) f = f := 
begin 
  ext, -- By extenstionality, it is sufficient to prove the to_fun components of the morphism f and id when composed yields the original to_fun function
  refl, -- Our goal is transformed to `morphism.to_fun x = morphism.to_fun x` and both sides are definitonally equal 
end 

@[simp]
def mult_group.morphism.comp_assoc {K L M N: Type} [mult_group_str K] [mult_group_str L] [mult_group_str M] [mult_group_str N] (f : mult_Group.morphism K L) (g : mult_Group.morphism L M) (h : mult_Group.morphism M N) : 
  mult_Group.morphism.comp (mult_Group.morphism.comp h g) f =  mult_Group.morphism.comp h (mult_Group.morphism.comp g f) := 
begin 
  refl, -- The goal is resolved since both sides of the equal sign are defintionally equal
end   


instance cat_of_groups : large_category_str (mult_Group') := 
{ hom := λ X, λ Y, mult_Group.morphism X.carrier Y.carrier, -- we first must provide a function which takes `mult_Group' → mult_Group' → Type` 
  id := λ X, mult_group.morphism.id,  -- we first fix ` X : mult_Group' ` and next we provide a function ` X.carrier → X.carrier `  
  comp := λ X Y Z, λ f g , mult_Group.morphism.comp g f, -- we first fix ` X Y Z : mult_Group'` in the context and ` f: mult_Group.morphism X.carrier Y.carrier` and ` g : mult_Group.morphism Y.carrier Z.carrier ` in the context as well, we then must define composition of multiplicative group structures which is given by `mult_Group.morphism.comp g f` 
  id_comp' := by { -- our goal is to prove `∀ {X Y : mult_Group'} (f : X ⟶ Y), f ⊚ 𝟙 X = f` 
    intros X Y, -- we fix `X Y : mult_Group` in the context
    exact mult_group.morphism.id_comp}, -- in order to prove composition with the id function yields the original function, we use the previously defined lemma 
  comp_id' := by { -- our goal is to prove `∀ {X Y : mult_Group'} (f : X ⟶ Y), 𝟙 Y ⊚ f = f` 
    intros X Y, -- we fix `X Y : mult_Group'` in the context
    exact mult_group.morphism.comp_id}, -- in order to prove composition with the id function yields the original function, we use the previously defined lemma 
  comp_assoc' := by { -- our goal is to prove `∀ {W X Y Z : mult_Group'} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), h ⊚ g ⊚ f = h ⊚ (g ⊚ f)` 
    intros W X Y Z, -- we fix ` W X Y Z : mult_Group' ` in the context
    exact mult_group.morphism.comp_assoc,} -- in order to prove composition is associative, we use the previously defined lemma 
    }

/-! ## Q2  Show that a monoid action gives rise to a functor from the 
delooping category of the monoid to the category of types. 
You can show that by filling in for the sorry placeholder in below. -/




def delooping_monoid_action (A : Type) [M : mult_Monoid] [mult_monoid_action M.carrier A] : 
(delooping_cat M).carrier ⥤  Type* := 
{ obj := λ X, A, -- for this field we must provide an instance `(delooping_cat M).carrier → Type `
  mor := λ X Y, _inst_3.smul, -- we fix ` X Y : (delooping_cat M).carrier → Type` in the context, we then provide a function from `mult_monoid_action M.carrier A` 
  resp_id' := by { -- our goal is to solve ` ∀ (X : (delooping_cat M).carrier), mult_monoid_action.smul (𝟙 X) = 𝟙 A` 
  intro X, -- we fix ` X : (delooping_cat M).carrier ` in the context 
  simp [precategory_str.id], -- through simplification, ` 𝟙 A ` is reduced to `id` 
  have h₃: ∀ (x : A), mult_monoid_action.smul ( 1 : M.carrier ) x = x, by {exact _inst_3.one_smul'}, -- we create a proof in the context which proves the propostion `∀ (x : A), mult_monoid_action.smul 1 x = x` . The proof of this proposition derives from a property associated with mult_monoid_action
  funext,  -- since we are proving equality of functions, we evoke function extenstionality 
  simp, -- Through simplificatioin ` id x ` is reduced to ` x ` 
  have h₅ : 𝟙 X = ( 1 : M.carrier), by {refl,}, -- we introduce a proof in the context which proves `𝟙 X` and `( 1 : M.carrier)` are equal since this is known by defintion 
  rw h₅, -- there is `𝟙 X` in the goal and we want to replace it by `1` to prove that `mult_monoid_action.smul 1 x = x` since we know `h₅` says something about the goal 
  exact h₃ x,  -- the goal is resolved by invoking the proposition found in the context 
  },
  resp_comp' := by { -- our goal is to prove `∀ {X Y Z : (delooping_cat M).carrier} (f : X ⟶ Y) (g : Y ⟶ Z), mult_monoid_action.smul (g ⊚ f) = mult_monoid_action.smul g ⊚ mult_monoid_action.smul f` 
  intros X Y Z f g, -- we fix ` X Y Z : (delooping_cat M).carrier → Type` and ` f : X ⟶ Y ` and `g : Y ⟶ Z` in the context
  funext y, 
  rw ← _inst_3.mul_smul' f g y, 
  
  }
  }



/-! ## Question 4: The Arrow Category
Given a category 𝓒 we want to construct a new category whose objects are morphisms of 𝓒 and whose morphisms are commutative squares in 𝓒.
 -/

@[ext]
structure arrow_type (𝓒 : Type*) [small_category_str 𝓒] :=
(dom : 𝓒)
(cod : 𝓒)
(arrow : dom ⟶ cod)

#check arrow_type


local notation `𝔸𝕣` : 10 := arrow_type


@[ext]
structure arrow_type_hom {𝓒 : Type*}[small_category_str 𝓒] (α β : 𝔸𝕣 𝓒 ) :=
(top : α.dom ⟶ β.dom)
(bot : α.cod ⟶ β.cod)
(eq : β.arrow ⊚ top = bot ⊚ α.arrow)


#check arrow_type_hom

/-
Show that we can equip `𝓒[→]` with the structure of a category where morphisms of 𝓒 and whose morphisms are commutative squares in 𝓒.
-/


instance arrow_cat (𝓒 : Type*)[small_category_str 𝓒] : small_category_str (𝔸𝕣 𝓒) :=
{ hom := λ α, λ β, arrow_type_hom α β ,
  id := λ α, ⟨𝟙 α.dom, 𝟙 α.cod, by {simp,}⟩ , 
  comp := λ X Y Z, λ f, λ g, ⟨  -- we must define composition of arrow_type_hom and in order to do this we fix ` X Y Z : 𝔸𝕣 𝓒 ` and ` f : arrow_type_hom X Y` and ` g : arrow_type_hom Y Z` in the context and provide an instance of type arrow_type_hom which defines composition
    precategory_str.comp f.top g.top, -- for the first field, we compose the top function of the homomorphisms of f g 
  precategory_str.comp f.bot g.bot, -- for the second field, we compose the top function of the homomorphisms of f g 
  by { -- our goal is to prove `Z.arrow ⊚ (g.top ⊚ f.top) = g.bot ⊚ f.bot ⊚ X.arrow` 
  simp, -- through simplificaiton, the associativity of composition is utlized, in order to rewrite the goal as `Z.arrow ⊚ (g.top ⊚ f.top) = g.bot ⊚ (f.bot ⊚ X.arrow)` 
  have h₂: Y.arrow ⊚ f.top = f.bot ⊚ X.arrow , by {exact arrow_type_hom.eq f}, -- we create a proof in the context which proves the proposition ` Y.arrow ⊚ f.top = f.bot ⊚ X.arrow` which is proven by the `eq` property associated with the arrow_type_hom structure 
  have h₃: Z.arrow ⊚ g.top = g.bot ⊚ Y.arrow, by {exact arrow_type_hom.eq g}, -- we create a proof in the context which proves the proposition `Z.arrow ⊚ g.top = g.bot ⊚ Y.arrow` which is proven by the `eq` property associated ith the arrow_type_hom structure 
  rw ← h₂, -- there is `f.bot ⊚ X.arrow` in h₂ and we want to replace it by `Y.arrow ⊚ f.top` to prove that `Z.arrow ⊚ (g.top ⊚ f.top) = g.bot ⊚ (Y.arrow ⊚ f.top)` since we know `h₂` says something about the goal 
  have h₄: (Z.arrow ⊚ g.top) ⊚ f.top = Z.arrow ⊚ (g.top ⊚ f.top), by {exact category_str.comp_assoc f.top g.top Z.arrow},  -- we create a proof in the context that proves the associativity of composition which is a property associated with category_str 
  rw ← h₄, -- there is `Z.arrow ⊚ (g.top ⊚ f.top)` in the goal and we want to replace it by `(Z.arrow ⊚ g.top) ⊚ f.top` to prove that `Z.arrow ⊚ g.top ⊚ f.top = g.bot (Y.arrow ⊚ f.top)` since we know `h₄` says something about the goal 
  rw h₃, -- there is `Z.arrow ⊚ g.top` in the goal and we want to replace it by `g.bot ⊚ Y.arrow` to prove that `g.bot ⊚ Y.arrow ⊚ f.top = g.bot ⊚ (Y.arrow ⊚ f.top)` since we know `h₃` says something about the goal 
  exact category_str.comp_assoc f.top Y.arrow g.bot,  -- a property associated with category_str is the associativity of composition which is required to resolve the goal 
   }
   ⟩ ,
  id_comp' := by { -- our goal is to prove `∀ {X Y : 𝔸𝕣 𝓒} (f : X ⟶ Y), f ⊚ 𝟙 X = f` 
  intros X Y f,  -- we fix ` X Y : 𝔸𝕣 𝓒` and ` f : X ⟶ Y ` in the context
  simp, -- Through simplification, properties concerning the composition of 𝟙 and the components of the arrow_type_hom is broken down
  ext, -- By extensionality, we can prove the homomorphisms are equal by proving the f.top functions are equal and the f.bottom functions are equal 
  {
    refl, -- Both sides of the propostion are definitionally equal, therefore the goal is resolved
  } ,
  {
    refl, -- Both sides of the propostion are definitionally equal, therefore the goal is resolved
  },
   },
  comp_id' := by { -- our goal is to prove `∀ {X Y : 𝔸𝕣 𝓒} (f : X ⟶ Y), 𝟙 Y ⊚ f = f`
  intros X Y f, -- we fix ` X Y : 𝔸𝕣 𝓒` and ` f : X ⟶ Y ` in the context
  simp,  -- Through simplification, properties concerning the composition of 𝟙 and the components of the arrow_type_hom is broken down
  ext,  -- By extensionality, we can prove the homomorphisms are equal by proving the f.top functions are equal and the f.bottom functions are equal 
  {
    refl, -- Both sides of the propostion are definitionally equal, therefore the goal is resolved
  } ,
  {
    refl, -- Both sides of the propostion are definitionally equal, therefore the goal is resolved
  },
  },
  comp_assoc' := by { -- our goal is to prove ` ∀ {W X Y Z : 𝔸𝕣 𝓒} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), h ⊚ g ⊚ f = h ⊚ (g ⊚ f)` 
  intros Q X Y Z f g h, -- we fix ` Q X Y Z : 𝔸𝕣 𝓒 ` and ` f : W ⟶ X`  `g :X ⟶ Y`  `h :  Y ⟶ Z`  in the context
  ext,  -- By extensionality, we can prove the homomorphisms are equal by proving the f.top functions are equal and the f.bottom functions are equal 
  {
    exact category_str.comp_assoc f.top g.top h.top, -- we invoke the property that composition is associative associated with category_str
  },
  {
    exact category_str.comp_assoc f.bot g.bot h.bot, -- we invoke the property that composition is associative associated with category_str
  },
  }, 
  }



/-
We shall define two functors form `𝔸𝕣 𝓒` to `𝓒`: `Dom` and `Cod`. `Dom` takes an arrow `f : X ⟶ Y` to its domain `X` and `Cod` takes `f` to `Y`.
-/


def Dom (𝓒 : Type*)[small_category_str 𝓒] :
  (𝔸𝕣 𝓒) ⥤ 𝓒 :=
{ obj := λ α, α.dom, 
  mor := λ X Y, λ f, arrow_type_hom.top f, -- we fix ` X Y : 𝔸𝕣 𝓒` in the context `f : X ⟶ Y` and provide a function from `X.dom ⟶ Y.dom` which is satisfied through the top function associated with arrow_type_hom structure
  resp_id' := by {-- our goal is to prove ` ∀ (X : 𝔸𝕣 𝓒), (𝟙 X).top = 𝟙 X.dom`
    intro X, -- we fix ` X : 𝔸𝕣 𝓒 ` in the context
  simp only [precategory_str.id]}, -- we resolve the goal through simplification of the id function associatiated with the precategory_str
  resp_comp' := by { -- our goal is to prove `∀ {X Y Z : 𝔸𝕣 𝓒} (f : X ⟶ Y) (g : Y ⟶ Z), (g ⊚ f).top = g.top ⊚ f.top`
    intros A B C f g, -- we fix ` A B C : 𝔸𝕣 𝓒 ` in the context ` f: A  ⟶ B ` and ` g : B ⟶ C ` in the context
    simp only [precategory_str.comp],}, } -- we resolve the goal through simplification of the defntion of composition associated with the pre_category_str


def Cod (𝓒 : Type*)[small_category_str 𝓒] :
  (𝔸𝕣 𝓒) ⥤ 𝓒 :=
{ obj := λ α, α.cod,
  mor := λ X Y, λ f, arrow_type_hom.bot f, -- we fix ` X Y : 𝔸𝕣 𝓒` in the context `f : X ⟶ Y` and provide a function from `X.cod → Y.cod` which is satisfied through the top function associated with arrow_type_hom structure
  resp_id' := by { -- our goal is to prove `∀ (X : 𝔸𝕣 𝓒), (𝟙 X).bot = 𝟙 X.cod` 
  intro X, -- we fix ` X :  𝔸𝕣 𝓒 ` in the context 
  simp only [precategory_str.id]}, -- we resolve the goal through simplification of the id function associatiated with the precategory_str
  resp_comp' := by { -- our goal is to prove `∀ {X Y Z : 𝔸𝕣 𝓒} (f : X ⟶ Y) (g : Y ⟶ Z), (g ⊚ f).bot = g.bot ⊚ f.bot`
  intros A B C f g,  -- we fix ` A B C : 𝔸𝕣 𝓒 ` in the context ` f: A  ⟶ B ` and ` g : B ⟶ C ` in the context
  simp only [precategory_str.comp], --  -- we resolve the goal through simplification of the defntion of composition associated with the pre_category_str
  }, }



/- Theorem:
For functors `F G : 𝓒 ⥤ 𝓓`, the type of natural transformations `F ⟶ G` is equivalent to the type of functors `𝓒 ⥤ 𝔸𝕣 𝓓`  whose composition with `Dom` and `Cod` are equal to `F` and `G` respectively.

Therefore, the arrow category classifies natural transformations.
-/

local notation F ` ⊚⊚ `:80 G:80 := category_str.functor.comp G F



def arrow_cat_classifies_nat_trans {𝓒 𝓓 : Type*}[small_category_str 𝓒] [small_category_str 𝓓] (F G : 𝓒 ⥤ 𝓓) :
(F ⟶ G) ≅ { H : 𝓒 ⥤ 𝔸𝕣 𝓓 // ( (Dom 𝓓) ⊚⊚ H = F ) ∧ ((Cod 𝓓) ⊚⊚ H = G) }  :=
{ to_mor := λ f,
⟨ {
  obj := λ a, ⟨F.obj a, G.obj a, nat_trans.cmpt F.obj G.obj⟩ ,
  mor := λ X Y f, sorry,
  resp_id' := sorry, 
  resp_comp' := sorry, 
}, 
by {split, 
{

},
{

},
} 
⟩,
  inv_mor := λ f,
⟨ {
  obj := λ a,,
  mor := λ X Y f, sorry,
  resp_id' := sorry, 
  resp_comp' := sorry, 
}, 
by {split, 
{

},
{

},
} 
⟩,
,
  left_inv := _,
  right_inv := _ }


/-! ## Question 3: Yoneda Problem -/


open nat_trans

def Yoneda (X Y : 𝓒) (α : ℍom.obj X ≅  ℍom.obj Y) : 
  X ≅ Y :=
{ 
  to_mor := α.to_mor.cmpt (op X) (𝟙 X),
  inv_mor := α.inv_mor.cmpt (op Y) (𝟙 Y),
  left_inv := by { have h₁, from α.inv_mor.naturality (α.to_mor.cmpt (op X) (𝟙 X)), 
  simp at h₁, 

  sorry, },
  right_inv := sorry, 
}



















