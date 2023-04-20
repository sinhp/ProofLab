-- import tactic.basic
import ..prooflab
import lectures.lec16_categories_basic
import lectures.lec17_functors
import lectures.lec18_nat_trans

open PROOFS
open PROOFS.STR
open category_str
open functor
open nat_trans


--Question 1




--Question 2
class mult_monoid_action (M A : Type) [mult_monoid_str M] :=
(smul : M → A → A) -- the scalar multiplication of `M` on `A`.
(one_smul' : ∀ (x : A), smul (1 : M) x = x)
(mul_smul' : ∀ (r s : M) (x : A),
smul (r * s)  x = smul r (smul s x))


def delooping_monoid_action (A : Type) [M : mult_Monoid] [mult_monoid_action M.carrier A] : (delooping_cat M).carrier ⥤  Type* :=
{ obj := λ x, A,
  mor := λ fx, λ fy, _inst_1.smul,
  resp_id' := by {intro X, funext, apply _inst_1.one_smul',},
  resp_comp' := by {intros X Y Z fxy gyz, -- use intro rule for for all
                    funext, -- use function extensionality
                    have h₁ : (mult_monoid_action.smul gyz) x =  (mult_monoid_action.smul gyz x), by {sorry},
                    rw h₁,
                    rw ← _inst_1.mul_smul' fxy gyz x,} } -- both sides of equation are equal

#check precategory_str.comp

--Question 3
universe u
def opposite (𝓒 : Type u) : Type u := 𝓒

def Yoneda (X Y : 𝓒) (α : ℍom.obj X ≅ ℍom.obj Y) : 
  X ≅ Y :=
{ 
  to_mor := α.to_mor.cmpt (op X) (𝟙 X),
  inv_mor := α.inv_mor.cmpt (op Y) (𝟙 Y),
  left_inv := sorry,
  right_inv := sorry, 
}


--Question 4
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


#check arrow_type_hom

/-
Show that we can equip `𝓒[→]` with the structure of a category where morphisms of 𝓒 and whose morphisms are commutative squares in 𝓒.
-/


instance arrow_cat (𝓒 : Type*)[small_category_str 𝓒] : small_category_str (𝔸𝕣 𝓒) :=
{ hom := λ α, λ β, arrow_type_hom α β ,
  id := λ α, ⟨𝟙 α.dom, 𝟙 α.cod, by {simp,}⟩ ,
  comp := sorry,
  id_comp' := sorry,
  comp_id' := sorry,
  comp_assoc' := sorry, }



/-
We shall define two functors form `𝔸𝕣 𝓒` to `𝓒`: `Dom` and `Cod`. `Dom` takes an arrow `f : X ⟶ Y` to its domain `X` and `Cod` takes `f` to `Y`.
-/


def Dom (𝓒 : Type*)[small_category_str 𝓒] :
  (𝔸𝕣 𝓒) ⥤ 𝓒 :=
{ obj := λ α, α.dom,
  mor := sorry,
  resp_id' := sorry,
  resp_comp' := sorry, }


def Cod (𝓒 : Type*)[small_category_str 𝓒] :
  (𝔸𝕣 𝓒) ⥤ 𝓒 :=
{ obj := λ α, α.cod,
  mor := sorry,
  resp_id' := sorry,
  resp_comp' := sorry, }



/- Theorem:
For functors `F G : 𝓒 ⥤ 𝓓`, the type of natural transformations `F ⟶ G` is equivalent to the type of functors `𝓒 ⥤ 𝔸𝕣 𝓓`  whose composition with `Dom` and `Cod` are equal to `F` and `G` respectively.

Therefore, the arrow category classifies natural transformations.
-/

local notation F ` ⊚⊚ `:80 G:80 := category_str.functor.comp G F



def arrow_cat_classifies_nat_trans {𝓒 𝓓 : Type*}[small_category_str 𝓒] [small_category_str 𝓓] (F G : 𝓒 ⥤ 𝓓) :
(F ⟶ G) ≅ { H : 𝓒 ⥤ 𝔸𝕣 𝓓 // ( (Dom 𝓓) ⊚⊚ H = F ) ∧ ((Cod 𝓓) ⊚⊚ H = G) }  :=
sorry




