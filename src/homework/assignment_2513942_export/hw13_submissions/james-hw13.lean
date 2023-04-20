import ..prooflab
import lectures.lec18_nat_trans
import tactic.basic

--open PROOFS
open PROOFS.STR

open category_str

--Q1
--Let's do this for additive groups. multiplicative groups are basically the same
--We have defined the type of additve groups
#check additive_Group

universe u
--we need to define the morphism between additive groups
--let's define it like we did for additive_monoid
@[ext]
class additive_monoid.morphism (M : Type u) (N : Type u) [additive_monoid_str M] [additive_monoid_str N] :=
(to_fun : M → N) -- f : M → N -- the underlying function of morphism
(resp_zero : to_fun 0 = 0) -- f (1_M ) = 1_N
(resp_add : ∀ x y : M, to_fun (x + y) = to_fun x + to_fun y) -- f(x *_M y) = (f x) *_N (f y)

@[ext]
class additive_group.morphism (M : Type u) (N : Type u) [additive_group_str M] [additive_group_str N] :=
(to_fun : M → N) -- f : M → N -- the underlying function of morphism
(resp_zero : to_fun 0 = 0) -- f (1_M ) = 1_N
(resp_add : ∀ x y : M, to_fun (x + y) = to_fun x + to_fun y) -- f(x *_M y) = (f x) *_N (f y)

--let's also define identity
def additive_group.morphism.id {M : Type}[additive_group_str M] : additive_group.morphism M M := 
{
  to_fun := id, --just identity
  resp_zero := by {simp}, --simplify by previous lemmas
  resp_add := by {simp}, --same here
}

--we also need composition
@[simp]
def additive_group.morphism.comp {L M N : Type} [additive_group_str L] [additive_group_str M] [additive_group_str N] (g : additive_group.morphism M N) (f : additive_group.morphism L M) : additive_group.morphism L N := 
{ to_fun := g.to_fun ∘ f.to_fun, --compose the to_funs
  resp_zero := by 
  {
    dsimp, --simplify by definition
    rw f.resp_zero, --use the individual properties of the morphisms to get to the goal
    rw g.resp_zero,
  },
  resp_add := by 
  {
    intros x y, --introduction for ∀
    dsimp, --simplfy by definition
    rw f.resp_add, --again, rewrite using individual properties
    rw g.resp_add,
  }, 
  }

--let's prove id_comp comp_id, and comp_assoc

--id_comp
@[simp]
lemma additive_group.morphism.id_comp {L M : Type} [additive_group_str L] [additive_group_str M]  (f : additive_group.morphism L M)  : 
  additive_group.morphism.comp additive_group.morphism.id f = f :=
begin 
  ext, --apply extensionality
  refl, --lhs is exactly rhs
end 

--comp_id
@[simp]
lemma additive_group.morphism.comp_id {L M : Type} [additive_group_str L] [additive_group_str M]  (f : additive_group.morphism L M)  : 
  additive_group.morphism.comp f additive_group.morphism.id = f := 
begin 
  ext, --apply extensionality
  refl, --lhs is exactly rhs
end

--comp_assoc
@[simp]
def additive_group.morphism.comp_assoc {K L M N: Type} [additive_group_str K] [additive_group_str L] [additive_group_str M] [additive_group_str N] (f : additive_group.morphism K L) (g : additive_group.morphism L M) (h : additive_group.morphism M N) : 
  additive_group.morphism.comp (additive_group.morphism.comp h g) f = additive_group.morphism.comp h (additive_group.morphism.comp g f) := 
begin 
  refl, --after simplifcation lhs is exactly rhs
end   

instance cat_of_additive_groups : large_category_str (additive_Group) :=
{ hom := λ X Y, additive_group.morphism X.carrier Y.carrier, --morphisms are additive_group.morphisms
  id := λ X, additive_group.morphism.id, --identiy is identity
  comp := λ X Y Z f g, additive_group.morphism.comp g f, --composition is defined above
  id_comp' := by {intros X Y f, apply additive_group.morphism.id_comp}, --proved above
  comp_id' := by {intros X Y f, apply additive_group.morphism.comp_id}, --proved above
  comp_assoc' := by {intros X Y Z W f g h, apply additive_group.morphism.comp_assoc}, --again, proved above
}

--Q2
@[ext]
class mult_monoid_action (M A : Type) [mult_monoid_str M] :=
(smul : M → A → A) -- the scalar multiplication of `M` on `A`.
(one_smul' : ∀ (x : A), smul (1 : M) x = x)
(mul_smul' : ∀ (r s : M) (x : A),
smul (r * s)  x = smul r (smul s x))

--Show that a monoid action gives rise to a functor from the delooping category of the monoid to the category of types. You can show that by filling in for the sorry placeholder in below.
set_option trace.simp_lemmas true

def delooping_monoid_action (A : Type) [M : mult_Monoid] [mult_monoid_action M.carrier A] : (delooping_cat M).carrier ⥤ Type* :=  
{ obj := λ Y, A, --element of delooping monoid to element of type
  mor := λ X Y (m : M.carrier), λ a, mult_monoid_action.smul m a, --map unit morphism to function in A. use the scalar multiplication above to send a : A to the action of m on a (still A)
  resp_id' := by 
  {
    intro X, --introduction for ∀
    cases X, --extract the properties of X
    funext, --function extensionality
    apply mult_monoid_action.one_smul', --this is one_mul of the monoid action
  },
  resp_comp' := by 
  {
    intros X Y Z f g, --introduction for ∀
    cases X, --extract the properties of X Y Z
    cases Y,
    cases Z,
    simp only [precategory_str.comp], --simplify by how we defined composition
    funext, --function extensionality
    dsimp, --simplify by definition
    rw ← mult_monoid_action.mul_smul', --rw the rhs as defined in mult_monoid_action.mul_smul'
    sorry, 
  },
}

--Q3 Yoneda

open nat_trans

local notation f ` ⊚ `:80 g:80 := precategory_str.comp g f    -- type as \oo

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {𝓒 : Type u₁} [category_str.{v₁} 𝓒] {𝓓 : Type u₂} [category_str.{v₂} 𝓓]

def Yoneda (X Y : 𝓒) (α : category_str.equiv (ℍom.obj X) (ℍom.obj Y)) : 
  category_str.equiv X Y :=
{
  to_mor := α.to_mor.cmpt (op X) (𝟙 X),
  inv_mor := α.inv_mor.cmpt (op Y) (𝟙 Y),
  left_inv := by
  {
    have h₁, from α.inv_mor.naturality (α.to_mor.cmpt (op X) (𝟙 X)),
    simp at h₁,
    cases α,
    cases α_to_mor,
    cases α_inv_mor,
    simp at *,
    sorry,

  },
  right_inv := by
  {
    sorry,
  },
}


--Q4
/-! ## The Arrow Category :
Given a category 𝓒 we want to construct a new category whose objects are morphisms of 𝓒 and whose morphisms are commutative squares in 𝓒.
 -/

-- @[ext]
-- structure arrow_type (𝓒 : Type*) [small_category_str 𝓒] :=
-- (dom : 𝓒)
-- (cod : 𝓒)
-- (arrow : dom ⟶ cod)

-- #check arrow_type


local notation `𝔸𝕣` : 10 := arrow_type

-- @[ext]
-- structure arrow_type_hom {𝓒 : Type*}[small_category_str 𝓒] (α β : 𝔸𝕣 𝓒 ) :=
-- (top : α.dom ⟶ β.dom)
-- (bot : α.cod ⟶ β.cod)
-- (eq : β.arrow ⊚ top = bot ⊚ α.arrow)


-- #check arrow_type_hom

/-
Show that we can equip `𝓒[→]` with the structure of a category where morphisms of 𝓒 and whose morphisms are commutative squares in 𝓒.
-/

--added extensionality to functor and arrow structures.

instance arrow_cat (𝓒 : Type*)[small_category_str 𝓒] : small_category_str (𝔸𝕣 𝓒) :=
{ hom := λ α, λ β, arrow_type_hom α β ,
  id := λ α, ⟨𝟙 α.dom, 𝟙 α.cod, by {simp,}⟩ ,
  comp := by
  {
    intros X Y Z, --introduce X, Y, Z for for all
    intros f g, --introduce f, g for the implication
    cases f, --extract f components
    cases g, --extract g components
    exact
    ⟨
    g_top ⊚ f_top, --composed top is the composition of the top components
    g_bot ⊚ f_bot, --composed bot is the composition of the bottom components
    by 
    {
      simp, --simplify by how we defined compostion
      rw ←category_str.comp_assoc, --rewrite with the associativity of composition
      rw g_eq, --rewrite using g_eq
      rw category_str.comp_assoc, --use composition associativity again
      rw f_eq, --we can use f_eq to get the rhs to be the same as the lhs
    }
    ⟩, --done
  },
  id_comp' := 
  by
  {
    intros X Y f, --introduction for ∀
    cases f, --extract f components
    simp, --simplify by previous definitions and lemmas
  }
  ,
  comp_id' := 
  by
  {
    intros X Y f,  --introduction for ∀
    cases f, --extract f components
    simp, --simplify by previous definitions and lemmas
  },
  comp_assoc' := 
  by
  {
    intros W X Y Z f g h, --introduction for ∀
    cases f, --extract f,g,h components
    cases g,
    cases h,
    dsimp, --simplify by definition
    ext, --use extensionality of arrow_type_hom to prove equality
    {--top part
      dsimp, --simplify by definition
      apply category_str.comp_assoc, --this is composition associativity
    },
    {--bottom part
      dsimp, --simplify by definition
      apply category_str.comp_assoc, --again, composition associativity
    },
  }, }

#check category_str.comp_assoc


/-
We shall define two functors form `𝔸𝕣 𝓒` to `𝓒`: `Dom` and `Cod`. `Dom` takes an arrow `f : X ⟶ Y` to its domain `X` and `Cod` takes `f` to `Y`.
-/


def Dom (𝓒 : Type*)[small_category_str 𝓒] :
  (𝔸𝕣 𝓒) ⥤ 𝓒 :=
{ obj := λ α, α.dom,
  mor := λ α β f, f.top, --just the top morphism
  resp_id' := by
  {
    intro X, --introduction for ∀
    cases X, --extract X components
    dsimp, --simplify by definition
    refl, --reflexivity after simplification. the left identiy is the same as the right identity (both X_dom after stuff in lhs ().top)
  },
  resp_comp' := by 
  {
    intros X Y Z f g, --introduction for ∀
    cases f, --extract f,g components
    cases g,
    dsimp, --simplify by definition
    refl, --reflexivity after simplification. .top lhs gives you the composition on the rhs
  }
,}


def Cod (𝓒 : Type*)[small_category_str 𝓒] :
  (𝔸𝕣 𝓒) ⥤ 𝓒 :=
{ obj := λ α, α.cod,
  mor := λ α β f, f.bot, --similar to Dom, but we use the bottom morphism this time
  resp_id' := by
  {--the proof will be similar to the proof for Dom
    intro X, --introduction for ∀
    cases X, --extract X components
    dsimp, --simplify by definition
    refl, --reflexivity after simplification. the left identiy is the same as the right identity after taking .bot
  },
  resp_comp' := by 
  {
    intros X Y Z f g, --introduction for ∀
    cases f, --extract f,g components
    cases g,
    dsimp, --simplify by definition
    refl, --reflexivity after simplification. .bot lhs gives you the composition on the rhs
  }
,}



/- Theorem:
For functors `F G : 𝓒 ⥤ 𝓓`, the type of natural transformations `F ⟶ G` is equivalent to the type of functors `𝓒 ⥤ 𝔸𝕣 𝓓`  whose composition with `Dom` and `Cod` are equal to `F` and `G` respectively.

Therefore, the arrow category classifies natural transformations.
-/

local notation F ` ⊚⊚ `:80 G:80 := category_str.functor.comp G F



def arrow_cat_classifies_nat_trans {𝓒 𝓓 : Type*}[small_category_str 𝓒] [small_category_str 𝓓] (F G : 𝓒 ⥤ 𝓓) :
fun_equiv (F ⟶ G) ({ H : 𝓒 ⥤ 𝔸𝕣 𝓓 // ( (Dom 𝓓) ⊚⊚ H = F ) ∧ ((Cod 𝓓) ⊚⊚ H = G) })   :=

{ to_fun := λ X,
{
  val := 
          {
            obj := λ α, 
            {
              dom := F.obj α,
              cod := G.obj α,
              arrow := by {
                            cases X, --extract X components
                            exact X_cmpt α, --use the object map on α
                          },
            },

            mor := by {
                        intros α β f, --introduction for ∀
                        cases X, --extract X components
                        cases F, --extract F components
                        cases G, --extract G components
                        dsimp at *, --simplify by definitions
                        have h1 := F_mor f, --use the F morphism map on f
                        have h2 := G_mor f, --use the G morphism map on f
                        sorry,
                      },







            resp_id' := _,
            resp_comp' := _ 
          },
  property :=_,

},  


{val := 
  { obj := λ α, { dom := F.obj α, cod := G.obj α, arrow := --object morphisms on α
  by
  {
    cases X, --extract X components
    exact X_cmpt α, --use the object map on α
  },},
  mor := λ α β f, { top := F.map f, bot := G.map f,} --morphisms on f
  resp_id' := _,
  resp_comp' := _ }
,

  inv_fun := _,
  left_inv := _,
  right_inv := _ }



,




  inv_fun := _,
  left_inv := _,
  right_inv := _ }