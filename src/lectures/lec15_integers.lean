/- 
Integers
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec13_structures_on_gaussian_int
import lectures.lec14_inductive_naturals

import homework.hw11

/-
We will learn about the construction of __quotient by equivalence relation__. Your mission is to use this construction to develop integers from natural numbers. You do this by replacing the `sorry` placeholders in **challenges** below with your own solutions. 
-/





open PROOFS 
open PROOFS.STR 




namespace integers

/- 
Having constructed the type of integers `ℤ`, we can prove that there is  a surjection `mat × mat → ℤ` sending 
`(m, n)` to their difference `m - n`. Check for yourself that the pairs `(m, n)`
and `(k, l)` are sent to the same integer if and only if `m + l = n + k`.
However, we are not going to use Lean's type of integers, but we will define our own ad-hoc type of integers in order to learn about quotient types in the process.
-/


@[simp] 
def same_diff (a b : mat × mat) : Prop :=
a.1 + b.2 = b.1 + a.2 -- note that at this point, we can write `a.1 - a.2 = b.1 - b.2`, since we do not have the operation of additive inverse (i.e. `- a.2` does not make sense yet, since it is not defined for `mat`. However, if once we have additive inverses then `same_diff a b ↔ (a.1 - a.2 = b.1 - b.2)` which says that `a` and `b` have the same differences.  )   

#check same_diff -- `same_diff` is a binary relation on `mat × mat` 

#check same_diff (2,4) (1,3)

example : same_diff (2,4) (1,3) := 
begin
  simp, 
  refl, 
end 

#check add_left_cancel


class left_cancel_additive_monoid_str (M : Type) extends additive_monoid_str M :=
(left_cancel : ∀ a b c : M, a + b = a + c → b = c)


class right_cancel_additive_monoid_str (M : Type) extends additive_monoid_str M :=
(right_cancel : ∀ a b c : M, b + a = c + a → b = c)


instance : left_cancel_additive_monoid_str mat :=
{
left_cancel :=
by 
  {
    -- we want to show that for all a b c : mat if a + b = a + c then b = c.
    intros a b c habc, -- Suppose arbitrary a b c : mat are given such that a + b = a + c.
    induction a with d ihd, -- We do not have additive inverses in mat, and as such, we cannot simply subtract a from both sides of the equation. Therefore, we use induction on a.
    { -- the base case of induction
    simpa using habc, --simpa is combination of rw/simp combined with exact.
    },
    { -- the inductive step of induction
    rw [mat.succ_add, mat.succ_add] at habc, -- rewriting d.succ + b and d.succ + c as (d + b).succ and (d + c).succ respectively.
    simp at habc,
    apply ihd,
    exact habc,
    },
  }
}


lemma mat.add_left_cancel : 
  ∀ a b c : mat, a + b = a + c → b = c := 
begin
  exact mat.left_cancel_additive_monoid_str.left_cancel, 
end 






/-! ## Challenge  
Prove that the addition operation on `mat` is __right cancellative__. 
Hint: You might like to use the instance `left_cancel_additive_monoid_str mat` together with the commutativity of addition (which we proved before using induction).  
-/
instance : right_cancel_additive_monoid_str mat := 
sorry 




lemma mat.add_right_cancel : 
  ∀ a b c : mat, b + a =  c + a → b = c := 
begin
  sorry,  
end 





@[simp]
def add_mon_add_left_comm (M : Type) [additive_monoid_str M] := ∀ m n k : M, m + (n + k) = n + (m + k)


/-! ## Challenge
Prove that the addition operation on mat is __left commutative__ in the sense that for all `m n k : mat` we have `m + (n + k) = n + (m + k)`.
-/

@[simp]
lemma mat.add_left_comm :
  add_mon_add_left_comm mat :=
begin
  unfold add_mon_add_left_comm, 
  sorry, 
end




/-
It's nice to be able to rw to get rid of explicit occurrences of same_diff.So let's make two lemmas suitable for rewriting.
-/
@[simp]
lemma same_diff_defn (a b : mat × mat) :
same_diff a b ↔ (a.1 + b.2 = b.1 + a.2) :=
begin
refl,
end



-- The one below is more useful if you've already done `cases` on the pairs.
lemma same_diff_pairs_defn {a b c d : mat} : 
  same_diff (a,b) (c,d) ↔ a + d = c + b :=
begin
  refl,
end



/- In below we show that the binary relation `same_diff` is an equivalence relation.-/


def same_diff_rflx : reflexive same_diff :=
begin
  unfold reflexive, -- the same as rw 
  intro x, 
  rw same_diff,
end


def same_diff_symm : symmetric same_diff :=
begin
  intros x y,
  intro hxy, 
  rw same_diff at hxy, 
  rw same_diff,
  exact hxy.symm,  
end

-- an alternative proof
lemma same_diff_symm_alt : symmetric same_diff :=
begin
  rintro ⟨i, j⟩ ⟨k, l⟩ h,
  rw same_diff at h ⊢ ,
  simp at h ⊢, 
  symmetry,
  assumption,
end

-- to prove transitivity we need the following lemmas
#check add_left_cancel
#check mat.add_right_cancel
#check mat.add_assoc


/-! ## Challenge  
Prove that `same_diff` is a transitive relation.
-/

lemma same_diff_trans : transitive same_diff :=
begin
  rintros ⟨i, j⟩ ⟨k, l⟩ ⟨m, n⟩,
  repeat {rw same_diff},  
  dsimp, 
  intros h₁ h₂,
  suffices : (i + n) + (l + k) = (m + j) + (l + k),
    by {apply mat.add_right_cancel _ _ _ this},
  calc i + n + (l + k) = (i + l) + (k + n) : sorry
  ...                        = (k + j) + (m + l) : sorry
  ...                        = (m + j) + (l + k) : sorry,    
end



lemma same_diff_equiv : 
  equivalence same_diff := 
begin
  unfold equivalence, 
  repeat {split} , 
  exact same_diff_rflx, 
  exact same_diff_symm, 
  exact same_diff_trans, 
end   


/-
A __setoid__ structure on a type `X` is a tuple `⟨ρ, hρ⟩` where `ρ : X → X → Prop` is an binary relation and `hρ` a proof that `rho` is an equivalence relation. The relation `ρ` is supposed to tell us which elements of `X` are equivalent to each other.  
-/

#check setoid


/- 
We give `mat × mat` a setoid structure coming from the equivalence relation `same_diff`. 
-/ 



instance mat.setoid : setoid (mat × mat) := 
⟨same_diff, same_diff_equiv⟩
 



/- 
We can use `≈` notation. This notation is inherited from 
class has_equiv X := (equiv : X → X → Prop) and 

instance {X : Type} [setoid X] : has_equiv X :=
⟨setoid.r⟩
-/ 


example (x y : mat × mat) : x ≈ y ↔ same_diff x y :=
begin
  -- true by definition of instance `mat.setoid`
  refl,
end


/- 
`same_diff x y` and `x ≈ y` are definitionally equal but not syntactically equal, rather annoyingly, so we need two more lemmas enabling us to rewrite.
-/ 

@[simp] 
lemma equiv_def (a b : mat × mat) : 
  a ≈ b ↔ a.1 + b.2 = b.1 + a.2 :=
begin
  refl,
end

@[simp] 
lemma equiv_def_pair (a b c d : mat) : 
  (a,b) ≈ (c,d) ↔ a + d = c + b :=
begin
  refl, 
end   


example : ((3 : mat), (5 : mat) ) ≈ (4, 6) :=
begin
  rw equiv_def_pair, 
  refl, 
end





/-! ## Building Integers Out of Natural Numbers 
We can define integers out of natural numbers by the operation of taking the __quotient__ of the relation `same_diff`. Here's the idea: We essentially think of a pair `(m , n)`, where `m n : mat` as an "integer", namely by taking the "difference" `m - n`. Therefore, we stipulate that `1` corresponds to the  `(1, 0)` and `-1` corresponds to the pair `(0, 1)`. However, this is not a 1-1 correspondence; while every "integer" corresponds to a unique pair (the integer `k` corresponds to `(k, 0)` if `k` is nonnegative and to `(0, k)` if `k` is negative),  there are many pairs which correspond to the same integer. For instance the pairs of the form `(m, m)` all have the same difference, namely `0` and hence by our consideration correspond to the integer `0`. Can you find all pairs which correspond to the integer `-1`? Indeed, they are all pairs `(m , n)` where `m + 1 = n`. We would like to construct a type in which we can identify all pairs with the same difference, i.e. we want to force `(0, 0)`, `(1, 1)`, `(2, 2)`, etc to be the same in this new type. In this new type, therefore, there is a one-to-one correspondence between our idea of integers and the pairs of natural numbers. The operation of __quotient__ handles this identification. 
-/



/-! ## What is quotient, really? 

Let `X` be any type, and let `r` be an equivalence relation on `X`. It is mathematically common to form the __quotient__  `X/r`, that is, the type of elements of `X` "modulo" `r`. A term of `X/r` is called an __equivalence class__ and is denoted by `⟦x⟧` where `x : X`.  

The __universal property__ of quotients which is key to their use is the following: 

If `f : X → Y` is any function that __respects the equivalence relation__ in the sense that for every `x y : X`, the proposition `r x y` implies `f x = f y`, then the function `f : X → Y` __lifts__ to a function 
`g : X/r → Y ` defined on each equivalence class `⟦x⟧` by `g ⟦x⟧ = f x`. 
-/



-- Now we can take the quotient of the setoid `mat × mat` by the equivalence relation `same_diff`. 
def Int := quotient mat.setoid

#check Int




/- 
There is a function `mat × mat → Int` given by `quotient.mk` which maps a pair `(m, n) : mat × mat` to the equivalence class 
`⟦ (m, n) ⟧`. Our notation for `quotient.mk x` is `⟦x⟧`. 
-/
def one_two_pair : mat × mat := (1,2)

def one_two_int : Int := quotient.mk one_two_pair -- `one_two_integer` is morally "-1".

example : 
  one_two_int = ⟦ one_two_pair ⟧ :=
begin
  refl,
end

    

example (x y : mat × mat ) : x ≈ y → ⟦x⟧ = ⟦y⟧ :=
quotient.sound

example (x y : mat × mat) : ⟦x⟧ = ⟦y⟧ → x ≈ y :=
quotient.exact

example (x y : mat × mat) : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
quotient.eq


example : 
  ⟦ ((1,1) : mat × mat) ⟧ = ⟦ (2, 2) ⟧ := 
begin
  apply quotient.sound, 
  simp, 
end


/-
We define an auxiliary addition function on integers. 
-/
def add_aux (x y : mat × mat) : Int := ⟦(x.1 + y.1, x.2 + y.2)⟧

/- Note that this is not the final addition function we would like to have, since the output type is different than inputs type.-/
#check add_aux 

@[simp]
lemma add_aux_def (i j k l : mat) : add_aux (i, j) (k, l) = ⟦(i + k, j + l)⟧ :=
begin
  refl,
end



lemma add_aux_lemma : ∀ a b x y : mat × mat,
(a ≈ x) → (b ≈ y) → add_aux a b = add_aux x y :=
begin
  rintros ⟨i, j⟩ ⟨k, l⟩ ⟨m, n⟩ ⟨p, q⟩ h₁ h₂,
  repeat {rw add_aux_def},
  apply quotient.sound,
  rw equiv_def_pair at h₁ h₂ ⊢, 
  calc i + k + (n + q) = (i + n) + (k + q) : sorry
  ...                        = (m + j) + (p + l) : sorry
  ...                        = m + p + (j + l) : sorry
end



end integers
