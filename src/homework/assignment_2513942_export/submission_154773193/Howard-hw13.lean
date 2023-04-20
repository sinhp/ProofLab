/- 
*****
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec13_structures_on_gaussian_int
import lectures.lec14_inductive_naturals
import homework.hw11

import lectures.lec16_categories_basic

import lectures.lec13_structures_on_gaussian_int

import lectures.lec17_functors
import lectures.lec18_nat_trans

open PROOFS 
open PROOFS.STR 


universes v₁ v₂ v₃ v₄ u u₁ u₂ u₃ u₄

variables {𝓒 : Type u₁} [category_str.{v₁} 𝓒] {𝓓 : Type u₂} [category_str.{v₂} 𝓓]

namespace category_str


-- Problem 1

-- I define the group morphism the same as the monoid morphism. The monoid morphism requires that it respects the identity, respects the inverse function, and respects addition.

@[ext]
class additive_group_str.morphism (M : Type u) (N : Type u) [additive_group_str M] [additive_group_str N] :=
(to_fun : M → N)
(resp_zero : to_fun 0 = 0)
(resp_inv : ∀ x : M, additive_group_str.inv (to_fun x) = to_fun (additive_group_str.inv x))
(resp_add : ∀ x y : M, to_fun (x + y) = to_fun x + to_fun y)


infixr ` →g+ `:25 := additive_group_str.morphism

-- Here I defined an identity group morphism, which is the identity. All of the proofs of the properties are simple because, once you remove the `'to_fun/id` from each proposition, it is obviously true by refl.

def additive_Group.morphism.id {M : Type}[additive_group_str M] : M →g+ M := 
{
  to_fun := id,
  resp_zero := by {simp},
  resp_inv := by {simp,},
  resp_add := by {simp},
}

-- Here I am defining composition of group morphisms

@[simp]
def additive_Group.morphism.comp {L M N : Type u} [additive_group_str L] [additive_group_str M] [additive_group_str N] (g : additive_group_str.morphism M N) (f : L →g+ M) : L →g+ N := 
{ to_fun := g.to_fun ∘ f.to_fun, -- Intuitively, the function of the composition is the composisiton of each input morphism
  resp_zero := by {
    simp, -- Removes `∘` notation
    repeat {rw additive_group_str.morphism.resp_zero,}, -- Repetedly rewrite the function with 0 inputed as 0, because it respects 0.
  },
  resp_inv := by {
    simp, -- Removes `∘` notation
    intro x, -- Fix an `x` by the intro rule of forall
    repeat {rw additive_group_str.morphism.resp_inv}, -- Repetedly rewrite `f(-x)` as `-f(x)` because `f` respects negativity, until both sides are equal
  },
  resp_add := by {
  intros x y, -- Fix `x y : M` by intro rule of forall
  simp, -- Removes `∘` notation
  repeat {rw additive_group_str.morphism.resp_add,} -- Break each `f(x + y)` into `f(x) + f(y)` because `f` respects addition, until both sides are equal.
  }
}

instance cat_of_Grps : large_category_str (category_str.additive_Group) := 
{ 
  hom := λ X, λ Y, X.carrier →g+ Y.carrier, -- Defined as my additive group morphism
  id := λ X, additive_Group.morphism.id, -- My defined identity above
  comp := λ X, λ Y, λ Z, λ f, λ g, additive_Group.morphism.comp g f, -- My defined composition above
  id_comp' := by {
    intros X Y f, -- fix `X Y : additive_Group` and `f : X ⟶ Y` by intro rule of forall
    ext, -- Only non-prop field of my morphism is the function, so I must only prove both functions are equivilent
    refl, -- Both sides are definitionally equal
  },
  comp_id' := by {
    intros X Y f, -- fix `X Y : additive_Group` and `f : X ⟶ Y` by intro rule of forall
    ext, -- Only non-prop field of my morphism is the function, so I must only prove both functions are equivilent
    refl, -- Both sides are definitionally equal
  },
  comp_assoc' := by {
    intros W X Y Z f g h, -- Introduce an alphabet worth of variables by the intro rule of forall
    ext, -- Only non-prop field of my morphism is the function, so I must only prove both functions are equivilent
    refl, -- Both sides are definitionally equal
  } 
}



-- Problem 2

-- Here I just pulled the definition of a `mult_monoid_action` from `hw9`

class mult_monoid_action (M A : Type) [mult_monoid_str M] :=
(smul : M → A → A) -- the scalar multiplication of `M` on `A`.
(one_smul' : ∀ (x : A), smul (1 : M) x = x)
(mul_smul' : ∀ (r s : M) (x : A),
smul (r * s)  x = smul r (smul s x))

def delooping_monoid_action (A : Type) [M : mult_Monoid] [mult_monoid_action M.carrier A] : (delooping_cat M).carrier ⥤  Type* :=
{ obj :=λ _, unit, -- Since the carrier of delooping_cat M is of type `unit`, I figured I could just always send the one term in the type, `*`, to its own type
  mor := λ M N h, id, -- Since I am always sending `*` to `unit`, every morphism in `Type*` will be `unit ⟶ unit`, which is a function `unit → unit`, and since unit only has one term, that function can just be the identity.
  resp_id' := by {
    unfold precategory_str.id, -- Just unfolding what the id morphism is
    intro star, -- Assume an element in the carrier, which would just be `*` anyway, by the introduction rule of implication
    refl, -- `id` is obviously equal to `id`
  },
  resp_comp' := by {
    intros X Y Z, -- Introduce all the terms of type carrier by introduction rule of forall. This again feels redundant because they will all be `*`
    intros h₁ h₂, -- Assume two morphims between the introduced terms by introduction rule of implication. Again redundant because they are all just `id`
    simp, -- The right side is the composition of identities, obviously still an identity. 
  } }


local notation f ` ⊚ `:80 g:80 := precategory_str.comp g f

-- Problem 3

def Yoneda (X Y : 𝓒) (α : equiv (nat_trans.ℍom.obj X)  (nat_trans.ℍom.obj Y)) : 
  equiv X Y :=
{ 
  to_mor := α.to_mor.cmpt (op X) (𝟙 X),
  inv_mor := α.inv_mor.cmpt (op Y) (𝟙 Y),
  left_inv := by {
    -- I have definetly been defeated by this problem. I think the level of abstraction is just a little too much for me right now unfortunately. Here is where my mind goes to try to understand it. `α.to_mor` is a morphism between `nat_trans.ℍom.obj Y` and `nat_trans.ℍom.obj X` which are just `functor.corepresentable Y` and `functor.corepresentable X`. Since these objects are themselves functors, their morphism is a natural transformation. So we project out the `cmpt` of that transformation and with `(op X : 𝓒ᵒᵖ)` as the input. This gives us `(functor.corepresentable X).obj (op X) ⟶ (functor.corepresentable Y).obj (op X)`. This is the same at `(X ⟶ X) ⟶ (X ⟶ Y)`. I now notice that this is a function. This function takes in `(𝟙 X)` and outputs something of type `(X ⟶ Y)`. The same procedure works out for the `α.inv_mor` to get something of type `(Y ⟶ X)`. I feel like the answer involces getting `α.to_mor` next to `α.inv_mor` to apply ``α.left_inv`, but I have no idea how to do that. I have spent countless hours on this, and am nearing the deadline, so, with a heavy problem, I will have to take an incomplete on this problem.
    sorry,
  },
  right_inv := sorry, 
}



-- Problem 4

/-! ## The Arrow Category :
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
  comp := λ α, λ β, λ γ, λ f, λ g, 
  { top := g.top ⊚ f.top,
  bot := g.bot ⊚ f.bot,
  eq :=  by {
    simp,
    rw ← f.eq,
    rw ← category_str.comp_assoc,
    rw g.eq,
    rw category_str.comp_assoc,
  }}
  ,
  id_comp' := by {
    intros X Y, -- Fix `X Y : 𝔸𝕣 𝓒` by into rule of forall
    intro h, -- fix `h : X ⟶ Y` by intro rule of forall
    -- unfold precategory_str.comp,
    -- unfold precategory_str.id,
    simp, -- This simplification reveals what composition with `𝟙` really looks like
    ext, -- Here I apply extensionality on `Arrow_type_hom`
    repeat {unfold_projs, refl}, -- All goals become obviously reflexive after unfolding the projections
  },
  comp_id' := by {
    intros X Y, -- Fix `X Y : 𝔸𝕣 𝓒` by into rule of forall
    intro h, -- fix `h : X ⟶ Y` by intro rule of forall
    -- unfold precategory_str.comp,
    -- unfold precategory_str.id,
    simp, -- This simplification reveals what composition with `𝟙` really looks like
    ext, -- Here I apply extensionality on `Arrow_type_hom`
    repeat {unfold_projs, refl}, -- All goals become obviously reflexive after unfolding the projections
  },
  comp_assoc' := by {
    intros W X Y Z, -- Fix a ton of terms in `𝔸𝕣 𝓒` by intro rule of forall
    intros f g h, -- fix a ton of terms which are morphisms between previous introduced terms by intro rule of forall
    ext, -- Applie extensionality
    repeat {unfold_projs,}, -- Unfolds all the projections
    rw category_str.comp_assoc, -- This is just composition associativity of categories
    rw category_str.comp_assoc, -- same here3
  }}



/-
We shall define two functors form `𝔸𝕣 𝓒` to `𝓒`: `Dom` and `Cod`. `Dom` takes an arrow `f : X ⟶ Y` to its domain `X` and `Cod` takes `f` to `Y`.
-/


def Dom (𝓒 : Type*)[small_category_str 𝓒] :
  (𝔸𝕣 𝓒) ⥤ 𝓒 :=
{ obj := λ α, α.dom,
  mor := λ X Y, λ f, f.top,
  resp_id' := by {
    intro X, -- Fix `X : 𝔸𝕣 𝓒` by intro rule of forall
    unfold arrow_type_hom.top, -- unfolds the projection and both sides are equal by refl
  },
  resp_comp' := by {
    intros X Y Z, -- Fix `X Y Z : 𝔸𝕣 𝓒` by intro rule of forall
    intros f g, -- Fix `f g : X ⟶ Y` by intro rule of forall
    unfold arrow_type_hom.top, -- unfolds the projection and both sides are equal by refl
  }, }


def Cod (𝓒 : Type*)[small_category_str 𝓒] :
  (𝔸𝕣 𝓒) ⥤ 𝓒 :=
{ obj := λ α, α.cod,
  mor := λ X Y, λ f, f.bot,
  resp_id' := by {
    intro X, -- Fix `X : 𝔸𝕣 𝓒` by intro rule of forall
    unfold arrow_type_hom.bot, -- unfolds the projection and both sides are equal by refl
  },
  resp_comp' := by {
    intros X Y Z, -- Fix `X Y Z : 𝔸𝕣 𝓒` by intro rule of forall
    intros f g, -- Fix `f g : X ⟶ Y` by intro rule of forall
    unfold arrow_type_hom.bot, -- unfolds the projection and both sides are equal by refl
  }, }





/- Theorem:
For functors `F G : 𝓒 ⥤ 𝓓`, the type of natural transformations `F ⟶ G` is equivalent to the type of functors `𝓒 ⥤ 𝔸𝕣 𝓓`  whose composition with `Dom` and `Cod` are equal to `F` and `G` respectively.

Therefore, the arrow category classifies natural transformations.
-/


local notation F ` ⊚⊚ `:80 G:80 := category_str.functor.comp G F


#check functor.mor
#check heq
#check eq_rec_heq
#check heq.refl
#check nat_trans

def arrow_cat_classifies_nat_trans {𝓒 𝓓 : Type*}[small_category_str 𝓒] [small_category_str 𝓓] (F G : 𝓒 ⥤ 𝓓) :
equiv (F ⟶ G) { H : 𝓒 ⥤ 𝔸𝕣 𝓓 // ( (Dom 𝓓) ⊚⊚ H = F ) ∧ ((Cod 𝓓) ⊚⊚ H = G) }  :=
{ to_mor :=λ A, { -- I am giving a function instance, so here I start with a λ
  val := { -- Give the value of the subtype
    obj := λ X, ⟨F.obj X, G.obj X, A.cmpt X⟩, -- Choose an `obj` function
    mor := λ X Y, λ h, ⟨F.mor h, G.mor h,  by { -- Chose this as the morphism
      unfold arrow_type.arrow, -- Must prove the arrow morphism for this type. Unfolds the arrow projection
      exact A.naturality h, -- This is exactyl naturality of the assumed `nat_trans`
    }⟩, 
    resp_id' := by {
      intro X, -- Fix `X : 𝓒` by intro rule of forall
      ext, -- apply extensionality
      {
        unfold arrow_type_hom.top, -- Unfold projection
        show F.mor (𝟙 X) = 𝟙 (F.obj X), -- Restate goal more simply
        rw functor.resp_id, -- Use the fact that functors respect identity
      },
      {
        unfold arrow_type_hom.bot, -- Projection
        show G.mor (𝟙 X) = 𝟙 (G.obj X), -- Restatement
        rw functor.resp_id, -- Respects id
      },
    },
    resp_comp' := by {
      intros X Y Z, -- Intro rule of forall
      intros f g, -- Intro rule of forall
      ext, -- apply extensionality
      {
        unfold arrow_type_hom.top, -- Unfold projection
        rw functor.resp_comp, -- Respects composition
      },
      {
        unfold arrow_type_hom.bot, -- Unfolds projection
        rw functor.resp_comp, -- respects compistion
      },
    }
  },
  property := {
    left := by {
      unfold category_str.functor.comp, -- Unfolds what functor composition is
      unfold_projs, -- Unfold projections
      simp, -- Simplify some weird lambda calculus
      ext, -- Apply extensionality
      {
        refl, -- Definitionally equal
      },
      {
        refl, -- Definitionally equal
      },
      {
        simp, -- Simplify some structural notation
        intros a a', -- Intro rule of forall
        intro ha, -- Intro rule of →
        rw ha, -- rw `a` for `a'`
        refl, -- Both sides are now definitonally equal
      },
    },
    right := by {unfold category_str.functor.comp, -- Unfolds what functor composition is
      unfold_projs, -- Unfold projections
      simp, -- Simplify some weird lambda calculus
      ext, -- Apply extensionality
      {
        refl, -- Definitionally equal
      },
      {
        refl, -- Definitionally equal
      },
      {
        simp, -- Simplify some structural notation
        intros a a', -- Intro rule of forall
        intro ha, -- Intro rule of →
        rw ha, -- rw `a` for `a'`
        refl, -- Both sides are now definitonally equal
      },
  },
},
  inv_mor := λ A, {
    cmpt := λ X, (A.val.obj X).arrow, -- This is where I became stuck on this problem, and I will sadly have to take an incomplete with this one too. I simply can not conjure up a morphism of the required type. This one feels really close, because if I use one of the properties I assumed by `A`, it could substitute with the terms in the type definition, but I do not know how to do that in Lean. This homework was really tough, but this was definetly a super cool and fun first college course, so thank you!
  },
  left_inv := _,
  right_inv := _ 
}

end category_str