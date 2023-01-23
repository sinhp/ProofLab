import lectures.lec18_nat_trans

set_option trace.simplify.rewrite true
open category_str
open PROOFS.STR
open functor

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {𝓒 : Type u₁} [category_str.{v₁} 𝓒] {𝓓 : Type u₂} [category_str.{v₂} 𝓓] {𝓔 : Type u₃} [category_str.{v₃} 𝓔]{𝓕 : Type u₄} [category_str.{v₄} 𝓕]
local notation f ` ⊚ `:80 g:80 := precategory_str.comp g f
local notation ` 𝓙 ` : 15 :=  functor.representable 
local notation ` c𝓙 ` : 15 :=  functor.corepresentable 
local notation ` ≅ `:85 := equiv

def comp (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) : 𝓒 ⥤ 𝓔 :=
{
  obj := G.obj ∘ F.obj, 
  mor := λ X, λ Y, λ f, G.mor (F.mor f), 
  resp_id' := by {intro X, simp },
  resp_comp' := by {intros X Y Z f g, simp only [functor.resp_comp],},
}

local notation F ` ⊚⊚ `:80 G:80 := functor.comp G F 


def ℍom : 𝓒 ⥤ (𝓒ᵒᵖ ⥤ Type v₁) :=
{
  -- the action of ℍom on objects of 𝓒
  obj := λ X, c𝓙 X,
  -- the action of ℍom on morphisms of 𝓒
  mor := λ X Y, λ f, {
                      cmpt := λ W, λ g, f ⊚ g,
                      naturality' :=
                      by
                      {
                        intros U V k,
                        dsimp,
                        funext x,
                        change f ⊚ (x ⊚ (hom.unop k)) = (f ⊚ x) ⊚ (hom.unop k),
                        simp only [comp_assoc],
                      },
                     },
  -- ℍom is functorial, it respects identifies and compositions in 𝓒
  resp_id' := by {intro X, ext Y, simp, refl,},
  resp_comp' := by 
                  {
                    intros X Y Z f g,
                    ext U,
                    simp,
                    refl,
                  },
}
/-
 __Q1__
 Construct the type of all groups. Show that this type admits the structure of a (large) category where morphisms are group homomorphisms.
-/
instance str (𝓒 : Cat) : small_category_str.{v₁} 𝓒.carrier := 𝓒.str

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
  comp := sorry,
  id_comp' := sorry,
  comp_id' := sorry, 
 }
-- The instance of cat_of_cat is the large category which has proofs of homomorphisms, identity, composition and composition with identity. However, in order to make a group homomorphism a proof of this, we need to prove association with some sort of application like addition or multiplication, in which we would prove the addition symbol as addition of small categories, or multiplication, the zero, as an addition of a blank cateogory with nothing inside, associativity, and communitivity. This would admit a structure of a large category where morphisms, which are functions inside a small category_str, are also group homomorphisms, which map those same functions to another small category_str.
/-
__Q2__ 
Recall the definition of mult_monoid_action from HW10.
-/
class mult_monoid_action (M A : Type) [mult_monoid_str M] :=
(smul : M → A → A) -- the scalar multiplication of `M` on `A`.
(one_smul' : ∀ (x : A), smul (1 : M) x = x)
(mul_smul' : ∀ (r s : M) (x : A),
smul (r * s)  x = smul r (smul s x))
/-
Show that a monoid action gives rise to a functor from the delooping category of the monoid to the category of types. You can show that by filling in for the sorry placeholder in below.
-/



def delooping_monoid_action (A : Type) [M : mult_Monoid] [mult_monoid_action M.carrier A] : (delooping_cat M).carrier ⥤  Type* :=
{ 
  obj := sorry,
  mor := sorry,
  resp_id' := sorry,
  resp_comp' := sorry, 
}


--__Q3__
def Yoneda (X Y: 𝓒) (α :  ℍom.obj X ≅ ℍom.obj Y) :
  X ≅ Y :=
{
  to_mor := α.to_mor.cmpt (op X) (𝟙 X),
  inv_mor := α.inv_mor.cmpt (op Y) (𝟙 Y),
  left_inv := sorry,
  right_inv := sorry,
}

-- Don't know why the definition of ℍom isn't working, but I know to prove the left_inv and right_inv of equivalence, we need to use the universal property of functors, which are from the representable and corepresentable definitions, which hold the respect of identity and composition of category_str

/-
structure nat_trans (F G : 𝓒 ⥤ 𝓓) : Type (max u₁ v₂) :=
(cmpt : Π X : 𝓒, F.obj X ⟶ G.obj X) -- "cmp" short for "component"
(naturality' : ∀ ⦃X Y : 𝓒⦄ (f : X ⟶ Y), cmpt Y ⊚ (F.mor f) = (G.mor f)  ⊚ cmpt X . obviously) -- the naturality condition which says the square above commutes

def representable {𝓒 : Type*}[category_str 𝓒] (X : 𝓒) : 𝓒 ⥤ Type* :=
{ 
  obj := λ Y, X ⟶ Y,
  mor := λ Y Z f g, f ⊚ g,
  resp_id' := by {intro Y, funext, simp, refl, },
  resp_comp' := by {intros X Y Z f g, funext, simp, refl}, 
}

def corepresentable {𝓒 : Type*}[category_str 𝓒] (X : 𝓒) : 𝓒ᵒᵖ ⥤ Type* :=
{ 
  obj := λ Y, unop Y ⟶ X, -- want 𝓒-morphisms from `Y` to `X`
  mor := λ Y Z f g, g ⊚ (hom.unop f),
  resp_id' := by {intro Y, funext, simp only [unop_id], simp, refl,  },
  resp_comp' := by {intros U' V' W' f g, simp only [unop_comp], funext x, rw ← comp_assoc, refl, },
}
-/
-- __Q4__ The final question

/-! ## The Arrow Category :
Given a category 𝓒 we want to construct a new category whose objects are morphisms of 𝓒 and whose morphisms are commutative squares in 𝓒.
 -/


structure arrow_type (𝓒 : Type*) [small_category_str 𝓒] :=
(dom : 𝓒)
(cod : 𝓒)
(arrow : dom ⟶ cod)

#check arrow_type


local notation `𝔸𝕣` : 10 := arrow_type



structure arrow_type_hom {𝓒 : Type*}[small_category_str 𝓒] (α β : 𝔸𝕣 𝓒 ) :=
(top : α.dom ⟶ β.dom)
(bot : α.cod ⟶ β.cod)
(eq : β.arrow ⊚ top = bot ⊚ α.arrow)

-- The Arrow Category describes the relationship between objects and arrows in a category and is used to describe the structure of a category. We want to prove communitivity in the arrow category, which we can prove with the structure arrow_type_hom, in that equivalence would be the main benifit.

-- the morphisms are the arrow_type_hom.top and arrow_type_hom.bot when composed together in communitive manner give you equivalence.