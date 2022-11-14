/- 
Logic of Predicates 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

/- # New tactics unveiled in this lesson:

-/

/- # Goals of this lecture: 
1. Parsing quantifiers and reading their scope correctly.
2. Identify startegies for proving a quantified sentence in mathematics based on its logical structure.
3. Do the above using interactive Lean tactics.  
-/


import ..prooflab
import .lec6_proposition
import ..homework.hw5

-- TODO: write properties of affine points like being in the upper half plane, etc
--import .logic_prop -- importing is transitive, hence we have already imported proofs1 and proofs0.


set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true

namespace PROOFS




/-! ## Predicates  
__Predicates__ are varying propositions, that is they are propositions which depend on varibale(s) (parameters) from a domain of discourse on which are they are defined. Another name for predicate is __relation__. Depending on the context, we might choose one or the other. 

Suppose we want to express the idea of listing propositions
“2 is even”,
“4 is even”,
“6 is even”, etc.

This way, this is an impossible task to do in finite time. We cannot write infinite sentences in finite time/memory. Note that the information specified above is incomplete, nevertheless we got the idea since we understood the pattern: the next sentence in the list will be 
“8 is even”.

Frege showed us how to do this: 
let `P` be the predicate with the domain `ℕ` of natural numbers and let `P(n)` be the proposition “n is even”. 

In Lean, we model predicates by functions into the type `Prop` of propositions. A __unary__ predicate `P` on a domain `X`, therefore, is a function `P : X → Prop` . Here `X` is said to be the __domain of discourse__ of `P` or simply the __domain__ of `P`. Note that `P`, upon taking a variables `x : X`, outputs a proposition `P(x)`. 
-/

variables {X Y Z : Type}


variables A B : X → Prop -- two predictes A and B on X 
-- We can think of A and B as a family of proposition in the sense that for each `x : X`, we get a proposition `A x`

section 
variables x y : X
#check A x -- this is a proposition
#check A x → B y -- this is a proposition
end 

section 
variable n : ℕ 
#check is_even -- a unary predicate on natural number
#check is_even n -- for each natual number we get a proposition 
#check is_odd
end 
/-
As before, the `variable` command does not create anything new. When we use variable `A` later in the file (say as part of an example), Lean creates a temporary variable of the type `A : X → Prop` (for that example).
-/



/-
A __binary predicate__/__relation__ has the type `X → X → Prop`. 
-/

variable C : X → X → Prop


/- 
Here `C`, upon taking a variables `x` and `y`, outputs proposition `C x y`. Binary predicates/relations provide us with means to talk about relationships between two things: 
Here's An example of a binary relation
-/
section love
variable person : Type 
variable loves : person → person → Prop 
variable Romeo : person 
variable Julliet : person 
#check loves Romeo Julliet
end love


-- non-equality is a binary predicate 
@[reducible] 
def neq {X : Type} (x y : X) := ¬ (x = y)
-- infix ` ≠ `:60 := neq


#check neq 
#check @neq
#check neq 2 3
#check 2 ≠ 3 -- syntactically the same as `neq 2 3`


lemma two_not_three : 
  2 ≠ 3 := 
begin 
  linarith, 
end   

#check two_not_three

-- sometimes having a lemma stating the definition `neq` as an iff statement is helpful in using `neq` with tactic `rw` 
@[simp] 
lemma neq.def {X : Type} (x y : X) : x ≠ y = ¬ (x = y) := 
begin
  refl, 
end 





namespace neq

lemma intro {x y : X}(h : x = y → false) : 
  x ≠ y := 
begin  
  exact h,
end 


lemma elim {x y : X} (h : x ≠ y) : 
  x = y → false := 
begin
  exact h,
end 

-- irreflexivity of equality
lemma irfl {x : X} (h : x ≠ x) : 
  false := 
begin 
  apply h, 
  refl,
end 


lemma irfl_alt {x : X} (h : x ≠ x) : 
  false := 
begin 
  contradiction,
end 


-- symmetry of inequality
lemma symm {x y : X} (h : x ≠ y) : 
  y ≠ x :=
begin
  intro h₁,
  apply h, 
  rw h₁, 
end 
 
end neq


#check @neq 
#check @eq

#check @neq.irfl
#check @neq.symm
#check @neq.elim
#check irfl -- this does not work because the content of the namespace are only visible by calling the name of that namespace and non-accessible otherwise. 



/-! ## Quantifiers 
__Quantifiers__ turn unary predicates into propositions by quantifying over their domain. -/


/-! ### Universal Quantifier 
What makes first-order predicate logic powerful is that it allows us to make assertions using __quantifiers__. Consider the following statements:

  -  Every natural number is even or odd, but not both.
  -  If some natural number is even, then so is its square.

The words "every" and "some" are encoded into the logic with the symbols `∀` and `∃`, respectively and they come with their own inference rules. The symbol `∀` followed by a variable `x` encodes the phrase "for every x". In other words, it asserts that every value of `x` has the property that follows it. A complete formalization of the first sentence above is given by the formal sentence 

  `∀ n : ℕ, even(n) ∨ odd(n) ∧ ¬ (even(n) ∧ odd(n))`. 

Similarly, a complete formal sentence of the second sentence above is given by

  `∀ n : ℕ, is_even (n) → is_even (n^2)`. 

  Once we know `n : ℕ` the followins are propositions 
  - is_even (n)
  - is_even (n^2)
  - is_even (n) → is_even (n^2)
  - ∀ n : ℕ, is_even (n) → is_even (n^2)

-/


#check is_even -- a predicate on natural numbers 

#check is_even 3 -- the proposition `∃ k : ℕ, 3 = 2 * k` 
#check is_even 4 -- the proposition `∃ k : ℕ, 4 = 2 * k`


#check ∀ x : ℝ, 0 ≤ x → abs x = x --∀

section parsing
variable P : Prop

#check (∀ x, A x) → P
#check ∀ x, (A x → P)
#check ∀ x, A x → P
--The last two are synonymous.

#check ∀ x, A x → B x
#check (∀ x, A x) → B -- this is wrong because the implication is only between propositions, and `B` is a predicate. 
#check (∀ x, A x) → B x

#check ∃ x, (A x → P)
#check ∃ x, A x → P
--The last two are synonymous.

#check ∃ z, A z → B z
#check (∃ z, A z) → B z

--General rule: anything after "∃ x" or "∀ x" can use "x", unless the scope of ∃ or ∀ is restricted by parentheses.
end parsing


/- 
The __introduction__ and __elimination__ rules of `∀` are similar to those of `→`. 

We start with the __introduction__ rule: Suppose `A : X → Prop` is a predicate. To prove the proposition `∀ x, A x`, we need to prove that for any given `x : X`, the proposition `A x` holds. This means we first fix an arbitrary element `x` of `X` and then show that `A x` holds. 
In Lean, we use the tactic __intro__ in order to do this. Here's a general pattern of construcing a proof of `∀ x, A x` where `sorry` has to be replaced by a correct proof term depending on `A`. 
-/ 
example : ∀ x, A x :=
begin 
  intro x, -- we fix an arbitrary element `x` here. 
  show A x, from sorry, 
end   



example : 
  ∀ x : X, x = x := 
begin 
  intro x, -- we fix an arbitrary element `x` here. 
  refl, 
end 



/-
The __elimination rule__ of `∀` says that given a predicate `P : X → Prop`, if we know that `∀ x, P x` (i.e. `P` holds for every term of `X`) holds then for any particular `t : X` we have that `P t` holds. In Lean, if we have a proof `h : ∀ x, P x` and a term `t : X` then we simply apply `h` to the term `t` to get a proof `h t : P t`. 
-/

section forall_elim
variable h : ∀ x, A x
variable t : X -- `X` is the domain of discourse of `A : X → Prop`
-- specialize `h` to `t`
example : A t :=
-- we simply apply `h` to `a`
show A t, from h t
end forall_elim


-- an example of two eliminations and one introduction of ∀ 
example : 
  (∀ x, A x) → (∀ x, B x) → (∀ x, A x ∧ B x) :=
begin 
  intro hA, 
  intro hB, 
  intro x, -- intro for ∀ 
  split, 
  {
    exact hA x, -- elim for ∀ 
  },
  {
    exact hB x, --elim for ∀ 
  },
end 







theorem forall_impl : 
  (∀ x, A x → B x) → (∀ x, A x) → (∀ x, B x) := 
begin 
  intro hAB, 
  intro hA, 
  intro x, 
  have h₁ : A x, from hA x,
  have h₂ : A x → B x, from hAB x,
  exact h₂ h₁, 
end   


theorem forall_imp_alt : 
  (∀ x, A x → B x) → (∀ x, A x) → (∀ x, B x) := 
begin 
  intro hAB, 
  intro hA, 
  intro x, 
  apply hAB,
  sorry,
end   





@[reducible] 
def le_pred {X : Type} (A B : X → Prop) := ∀ x, A x → B x
local notation ` ≤ ` : 30 := λ A B, le_pred A B

#check A ≤ B




-- under the assumption `A ≤ B`, we can prove that if `A` is true everywhere, then `B` is true everywhere.  
example (h : A ≤ B) : 
  (∀ x, A x) → (∀ x, B x) := 
begin
  sorry,  
end 




/- 
A __binary relation__ on a type `X` is a two-variable predicate `R : X → X → Prop`, that is, a true-false statement `R x y` attached to each pair of elements of `X`.

In mathematics, we often use __infix notation__, writing 
`a R b` instead of `R a b`, e.g. `a = b`, `a ≤  b`, etc. Equality an inequality are relations.
-/ 


-- let X be a type, and let R be a binary relation on R.
variable {R : X → X → Prop}


/-
If `R` is reflexive, symmetric and transitive, we say it is an
__equivalence relation__. We will use the standard notation `x ≈ y` for `R x y` when `R` is an equivalence relation.

* __reflexivity__:  
`R x x`, for every `x` of `X`. 

* __transitivity__: 
If `R x y` and `R y z`, then `R x z`, for every `x y z` of `X`. 

* __symmetry__: 
If `R x y` then `R y x`, for every `x y` of `X`. 

In Lean: 
`reflexive R := ∀ (x : X), R x x`
`symmetric R := ∀ ⦃x y : X⦄, R x y → R y x`
`transitive R := ∀ ⦃x y z : X⦄, R x y → R y z → R x z`
`equivalence R := reflexive R ∧ symmetric R ∧ transitive R`
-/


#reduce reflexive R -- ∀ (x : X), R x x
#reduce symmetric R -- ∀ ⦃x y : X⦄, R x y → R y x
#reduce transitive R -- ∀ ⦃x y z : X⦄, R x y → R y z → R x z


lemma equivalnce.defn :
  equivalence R ↔ reflexive R ∧ symmetric R ∧ transitive R := 
begin
  refl,  
end   




namespace equivalence


lemma refl_ext_left {ρ : reflexive R} (x y : X) (H : ∀ a : X,  R a x → R a y) : 
  R x y :=
begin
  sorry, 
end 


lemma refl_ext {ρ : reflexive R} (x y : X) (H : ∀ a: X,  R x a ↔ R y a) : 
  R x y :=
begin
  sorry, 
end 



lemma refl_symm_ext_left {ρ : reflexive R} {σ : symmetric R} (x y : X) (H : ∀ a : X,  R x a → R y a) : 
  R x y :=
begin
  sorry, 
end    




theorem eqv_rel_ext {eqv : equivalence R} (x y : X) (H : ∀ a: X,  R x a → R y a) : R x y :=
begin 
obtain ⟨ρ, σ, τ⟩ := eqv, 
  sorry, 
end 



theorem trans_ext {tr : transitive R} (x y : X) (H : ∃ a : X, R x a ∧ R a y) : R x y := 
begin 
sorry, 
end 


end equivalence -- end of namespace






/-! ### Examples of Universal Quantifiers in Mathematics-/

/-
In the examples below, we use the introduction rule of `∀` to prove statements of the form `∀ x, P x`. 
-/

example : 
  ∀ x : ℝ, (0 ≤ x) → abs x = x := 
begin
  intro t, -- since we are introducing any arbitrary element of `ℝ` it does not matter whether we name it `x` or `t` or whatever. 
  intro h, -- application intro
  sorry,  
end




section 
variables a b : ℝ
#check (lt_rev_of_neg : a < b → -b < -a) -- this was proved in hw5
end 

lemma is_pos_abs : 
  ∀ x : ℝ, 0 ≤ abs x :=
begin
  intro x, 
  cases le_or_gt 0 x,
  {
    have h₁ : abs x = x, from abs_of_nonneg h,
    rw h₁, 
    exact h,
  },
  {
    have h₁ : abs x = - x, from abs_of_neg h,
    have h₂, from lt_rev_of_neg h, 
    rw neg_zero at h₂, 
    rw h₁, 
    apply le_of_lt,
    exact h₂,
  },
end   


/-
In the example below, we use the proof `is_pos_abs : ∀ x : ℝ, 0 ≤ abs x` from the above lemma to prove a new result accoring to the elimination rule of the universal quantifier. In the second branch of the prove below, 
we have `x: ℝ` with a proof `h: 0 > x` (which show `x` is negative) as our context. Therefore, we can apply `is_pos_abs` to that `x`. 
-/
-- leave 
example : 
  ∀  x : ℝ, x ≤ abs x := 
begin
  intro x, 
  cases le_or_gt 0 x,
  {
    apply le_of_eq, 
    apply eq.symm, 
    apply abs_of_nonneg,
    apply h, 
  },
  {
    apply le_of_lt,
    apply lt_of_lt_of_le,
    apply h,
    exact is_pos_abs x, 
  },
end 


/- 
A function f : A → B is __injective__ (also called __one-to-one__) whenever the following sentence holds.
  ` ∀ a, b : A,  f(a) = f(b) → a = b `
An injective function is said to be an __injection__.
-/

@[simp] def is_injective {X Y : Type} (f : X → Y) :=
∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂

-- what is @[simp]?
-- what is {}?
-- what is ⦃ ⦄?


lemma injection_respect_distinction {X Y : Type} {f : X → Y} (inj : is_injective f) : 
  ∀ ⦃x₁ x₂⦄, (x₁ ≠ x₂)  → (f x₁ ≠ f x₂) := 
begin
  sorry, 
end 








-- proof by contrapositive
example {X Y : Type} {f : X → Y} (inj : is_injective f) : 
  ∀ ⦃x₁ x₂⦄, (x₁ ≠ x₂)  → (f x₁ ≠ f x₂) := 
begin
  sorry,
end 








-- Let's prove that the **identity function is injective**: 
lemma injective_id : is_injective (id : X → X) :=
begin
   intros x₁ x₂, -- introduce variables for two inputs of x by the introduction rule of for all
  intro hid, -- introduce a proof of `id x₁ = id x₂` by the introduction rule of elimination
  exact hid, -- `id x₁` is definitionally identical to `x₁`, so `hid : id x₁ = id x₂` is identical to the goal `x₁ = x₂`
end




-- **Injections are closed under composition**, that is the composite of injective functions is injective. Here is a forward proof.
lemma injective_comp {X Y Z : Type} (f : X → Y) (g : Y → Z) (inj_f : is_injective f) (inj_g : is_injective g): 
  is_injective (g ∘ f) := 
begin
  unfold is_injective,
  -- since we are proving a ∀ sentence we need to use `intros`
  intros x x' h, 
  -- simplify the definition of composition in `h`
  dsimp at h, 
  -- we deduce f x = f x' from g(f x) = g(f x') since g is injective. 
  have h₂ : f x = f x', from inj_g h,  
  -- we deduce x = x' from f x = f x' since f in injective.
  exact inj_f h₂, 
end 

#check injective_comp

-- Here is a backward proof using `apply` tactic. 
example (f : X → Y) (g : Y → Z) (inj_f : is_injective f) (inj_g : is_injective g) : 
  is_injective (g ∘ f) :=
begin
  unfold is_injective at *, -- `at *` tells to unfold everywhere
  intros a b he, 
  apply inj_f, 
  apply inj_g, 
  exact he, 
end

/-
Yet another proof: Lean's unifier figures out which variables you must mean.
-/
example (f : X → Y) (g : Y → Z) (inj_f : is_injective f) (inj_g : is_injective g) : 
  is_injective (g ∘ f) :=
λ _ _, @@inj_f ∘ @@inj_g  



/- 
Let's prove that for every function `f : X → Y` and `g : Y → Z`, if the composition `g ∘ f : X → Z` is injective then `f` is injective.  
-/


lemma inj_right_of_inj_comp (f : X → Y) (g : Y → Z) (h : is_injective (g ∘ f)) :
  is_injective f := 
begin
  intros x₁ x₂ h₁, 
  have h₂ : (g ∘ f) x₁ = (g ∘ f) x₂, by
    {
      calc (g ∘ f) x₁   = (g ∘ f) x₂ : sorry, 
    },  
  sorry, 
end 







example :
  is_injective (swap_pair X Y) :=
begin
  sorry, 
end   


#check fst 
#check snd
#check congr_arg



/-
Using the universal qunatifier `∀` we define the concepts of __upper bound__ and __lower bound__.
-/

def is_real_val_fun_ub {X : Type} (f : X → ℝ) (a : ℝ) := 
∀ x : X, f x ≤ a 

def is_real_val_fun_lb {X : Type} (f : X → ℝ) (a : ℝ) := 
∀ x : X, a ≤ f x


variables f g : X → ℝ
variables a b : ℝ
#check is_real_val_fun_ub (f : X → ℝ) (a : ℝ)
-- we read `is_real_val_fun_ub (f : X → ℝ) (a : ℝ)` as " `a` is an upper bound for the real-valued function `f` ".
-- Similar `is_real_val_fun_lb {X : Type} (f : X → ℝ) (a : ℝ) ` is read as " `a` is a lower bound for the real-valued function `f` "

#check add_le_add

lemma lb_of_sum_of_sum_of_lb (h₁ : is_real_val_fun_lb f a) (h₂ : is_real_val_fun_lb g b) :
  is_real_val_fun_lb (λ x, f x + g x) (a + b) :=
begin
  sorry,
end

#check lb_of_sum_of_sum_of_lb
#check lb_of_sum_of_sum_of_lb f g a b


-- we could have ended the proof above more easily with `apply` rather than `exact`. 
example (h₁ : is_real_val_fun_lb f a) (h₂ : is_real_val_fun_lb g b) :
  is_real_val_fun_lb (λ x, f x + g x) (a + b) :=
begin
  sorry,
end


/- 
We read `nonneg_real_val_fun f` as "the real-valued function `f` has non-negative values." 
-/
def nonneg_real_val_fun {X : Type} (f : X → ℝ) := is_real_val_fun_lb f 0

#check nonneg_real_val_fun 
#check nonneg_real_val_fun f


-- what does the next lemma say?
lemma sum_nonneg_real_fun (nnf : nonneg_real_val_fun f) (nng : nonneg_real_val_fun g) :
  nonneg_real_val_fun (λ x, f x + g x) :=
begin
-- in order to prove a univerally quantified statement, we need 
-- let `x` be an arbitrary element of `X`
 intro x, 
-- to prove that `f x + g x` is nonnegative we need to prove that `f x` is nonnegative and `g x` is nonnegative   
  apply add_nonneg,
-- `f x` is nonnegative because ...   
  apply nnf,
-- `g x` is ... 
-- therefore we are done 
  sorry,
end

set_option trace.simp_lemmas true
--Alternatively, we could prove it using lemma `lb_of_sum_of_sum_of_lb`: 
example (nnf : nonneg_real_val_fun f) (nng : nonneg_real_val_fun g) :
  nonneg_real_val_fun (λ x, f x + g x) :=
begin
  sorry,
end


-- what does the next lemma say?
lemma mul_nonneg_real_fun (nnf : nonneg_real_val_fun f) (nng : nonneg_real_val_fun g) :
  nonneg_real_val_fun (λ x, f x * g x) :=
begin
  sorry,
end







/-! ### Existential Quantifier 

The __existential quantifier__ in logic encodes the phrase “there exists”. The formal expression `∃ x : ℕ, x ^ 2 = 9` says that there is a natural number whose square equals `9`. 
-/

/- Some examples of unary predicates on `ℕ` built from `∃` -/

-- def is_even (n : ℕ) := ∃ k , n = 2 * k    
-- def is_odd (n : ℕ ) := ∃ k , n = 2 * k + 1
def is_odd_alt (n : ℕ) := ¬ is_even n


/-
The canonical way to prove an existentially-quantified statement such as this one is to exhibit a natural number and show that it has the stated property. The number `3` has the required property, and the `refl` tactic can prove that it meets the stated property. 

__How to prove an `∃`-statement__: In Lean, in order to prove a statement of the form `∃ x, P x`, we exhibit some `a` using the tactic `use a` and then prove `P a` by other means. Sometimes, this `a` can be an object from the local context or a more complicated expression built from the stuff of the context.

t : X   ht : P (t)
----------------- (intro rule for ∃)
∃ x, P(x)

-/

example : 
  ∃ x : ℕ, x ^ 2 = 9 := 
begin 
  use 3, -- we want to prove `∃ x : ℕ, x ^ 2 = 9`. So, we use the intro rule of `∃`. Our candidate is 3.   
  refl,  
end 

example : 
  ∃ x : ℚ, 2 < x ∧ x < 3 :=
begin
  use 7 / 3,
  norm_num, -- what does norm_num do? 
end

-- term mode proof 
example : 
∃ x : ℚ , 2 < x ∧ x < 3 :=
⟨7 / 3, by norm_num⟩


example :
  is_even 10 := 
begin
  unfold is_even,
  use 5, 
  refl,
end   


example : 
  ∃ n , is_even n :=
begin
  unfold is_even,
  use 4, -- picking `3` would be unwise, since `is_even 3` would be impossible to prove.
  use 2, -- This time we have no choice but to pick `2`.
  refl, -- refl is good enough for proving equalities in `ℕ`.
end 



example {X Y : Type} (f : X → Y) (t : X): 
  ∃ y : Y, ∃ x : X, f x = y := 
begin
  use f t, -- we ae trying to prove `∃ y : Y, ∃ x : X, f x = y`, and for this we use the intro rule of existential quantifier. Our candidate for the intro rule is `t`. We now have to prove the property `∃ x : X, f x = y`  about `y := f t`
  use t, -- we ae trying to prove `∃ (x : X), f x = f t` and for this we use the intro rule of existential quantifier. Our candidate for the intro rule is `t`. 
  -- we need to prove f t = f t which is done by `refl`. 
end 



example : 
∃ (f : X → Y) (g : Y → Z),  is_injective (g ∘ f) ∧  ¬ is_injective g := 
begin
  sorry, 
end 




/- we know how to prove an exists statement. But how do we use one? 


               ---1
               P(t)
               ---
                .
                .
                .
               ---
∃ x, P(x)      R
---------------------- 1 , ∃-elim  
          R



When __using__ a proof of a statement of the form `∃ x : X, P x`, we can assume having `t : X` such that `P t` is true. If from a general `t` and a proof of `P t` we can prove `R` then we can prove `R` from `∃ x, P x`.

The corresponding Lean tactic is `cases ... with ...`. 
-/


#check (nat.succ_pos : ∀ (n : ℕ), 0 < nat.succ n)
#check (lt_irrefl)

example (x : ℕ) : 
  (∃ y : ℕ, y + 1 = x) → (x ≠ 0) :=
begin
  sorry, 
end   






--Challenge: without linarith 
example (x : ℕ) : 
  (∃ y : ℕ, y + 1 = x) → (x ≠ 0) :=
begin
  intro h, -- intro rule for → 
  cases h with y hy, -- the first use of `cases` for the elim rule of ∃
  intro hx, 
  have hy₁, from (nat.succ_pos y),  
  change 0 < y + 1 at hy₁, 
  rw hy at hy₁, 
  rw hx at hy₁, 
  apply lt_irrefl 0, 
  exact hy₁,
end   




example : 
  ¬ ∀ n , is_odd n :=
begin
  unfold is_odd,
  intro h, 
  have h₁ : ∃ (k : ℕ), 0 = 2 * k + 1, from h 0, 
  -- we need to use/eliminate `h₁`
  cases h₁ with n h₂,
  have h₃ : 0 < 2 * n + 1, from nat.succ_pos (2 * n),
  rw h₂ at h₃,
  apply lt_irrefl (2 * n + 1), -- `apply lt_irrefl` fails with the error ``invalid apply tactic, failed to synthesize type class instance for preorder ?m_1``
  exact h₃, 
  -- alternatively, finish it off by `linarith` after `h₂` without any `rw` or `apply`.
end 


/- 
An example of binary predicates on `ℕ` built from `∃` 
`divides m n` states that the natural number `m` divides natural number `n`. For instance 
-/

@[simp]
def divides (m n : ℕ) := ∃ k : ℕ, n = m * k
#check divides 

/- 
Be careful: the divisibility symbol is not the ordinary bar on your keyboard. Rather, it is a unicode character obtained by typing `\|` in VS Code. 
-/ 

-- by defn
example : 
  ∀ n : ℕ, divides 2 n ↔ is_even n := 
begin
  intro n, -- we want to prove the ∀ statement `∀ n : ℕ, divides 2 n ↔ is_even n`
  split, 
  {
    simp at *, 
    intro k, 
    intro h, 
    unfold is_even,
    use k, 
    exact h, 
  },
  {
    sorry,
  },
end   


lemma self_divide_self_sqr (x : ℕ) 
  : divides x (x^2) :=
begin 
 use x, 
 -- refl, 
 exact pow_two x,
end 



lemma divides_trans (x y z : ℕ) (h₀ : divides x y) (h₁ : divides y z) : 
  divides x z :=
begin
  unfold divides at *, 
  cases h₀ with k₀ hk₀, 
  cases h₁ with k₁ hk₁, 
  use k₀ * k₁, 
  rw [← mul_assoc, ← hk₀, hk₁],
end 


example (a b : ℕ) :
  divides  (a + b) ((a + b)^2) := 
begin
  apply self_divide_self_sqr, 
end   


/- 
__Combining ∀ and ∃__ to define prime numbers, surjective functions, etc:
-/


/-
 `prime n` means that `n` is a prime number, that is, a natural number at least 2 whose only divisors are `p` and `1`. 
-/

def is_prime (p : ℕ) := (2 ≤ p) ∧ ∀ m : ℕ, divides m p → m = 1 ∨ m = p
#check is_prime

def is_prime_alt₁ (p : ℕ) := 2 ≤ p ∧ ∀ m < p, divides m p → m = 1

def is_prime_alt₂ {p : ℕ} := 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬ divides m p 


#check ne_of_lt

lemma is_prime_ne_one : 
  ∀ p : ℕ,  is_prime p → p ≠ 1 
  :=
begin
intro p, 
intro hp,
cases hp, 
intro h₁, -- alternatively with `linarith`
rw h₁ at hp_left,
cases lt_or_eq_of_le hp_left with ludicrous nonsense, 
{
  have silly, from lt_trans (one_lt_two) ludicrous,
  apply lt_irrefl 1,
  exact silly,
},
{
  apply nat.add_self_ne_one 1,
  change 1 + 1 = 1 at nonsense, --rw does not work, see the lesson arithmetic with tactics. 
  exact nonsense,
},
end   


lemma nat_zero_or_atleast_one (k : ℕ) : 
  (k = 0) ∨ (1 ≤ k) := 
begin
  exact eq_zero_or_pos, -- i found this with suggest, but library-search did not work!
end 

lemma dvd_less (a b : ℕ) (h : divides a b) :
 (b ≠ 0) → a ≤ b := 
begin
  sorry,
end  


#check (nat.dvd_prime _).mp
lemma seven_is_prime :
  is_prime 7 :=
begin
  split,
  linarith,
  intro n, 
  intro hn, 
  sorry,
end 


-- but to show that `∀p prime₁ p  ↔ prime₂ p ` we need to know the rules of inference for quantifiers. 

example : 
  ∀ n : ℕ, is_prime n ↔ is_prime_alt₁ n := 
begin 
  intro p, 
  split, 
    {
      intro h, 
      unfold is_prime_alt₁, 
      unfold is_prime at h,
      split, 
        cases h, 
        exact h_left, 
        intro m, 
        intro hm, 
        intro hmp, 
        cases h, 
        have h', from h_right m hmp, 
        cases h', 
          exact h', 
          exfalso, 
          linarith,
    },      
    {
      intro h, 
      sorry,
    },   
end 


def is_surjective {X Y : Type} (f : X → Y) :=
∀ y : Y, ∃ x : X, f x = y 



-- Surjections are closed under composition.
lemma surj_comp (f : X → Y) (g : Y → Z) (surj_f : is_surjective f) (surj_g : is_surjective g): is_surjective (g ∘ f) := 
begin
  intro z,
  have h₁, from surj_g z,      
  cases h₁ with y h₂, 
  have h₃, from surj_f y, 
  cases h₃ with x h₄, 
  have h₅: g y = g (f (x)), by rw h₄, 
  have h₆ : z = g (f (x)), by rw [←h₂, h₅],   
  existsi x,
  rw h₆,  
end 

-- The proof above can be made more compact: we can combine two of the `have` and `cases` into one cases hg a with b hb ... 
-- also, much better rewrites. 







lemma surj_comp_alt (f : X → Y) (g : Y → Z)  (surj_f : is_surjective f) (surj_g : is_surjective g) : is_surjective (g ∘ f) :=
begin
  unfold is_surjective at *, -- We want to prove that `∀ (y : Z), ∃ (x : X), (g ∘ f) x = y` 
  intro z, -- We use the introduction rule of ∀ to fix `z : Z` and try to prove  `∃ (x : X), (g ∘ f) x = y` 
  have h₁, from surj_g z, -- by the elimination rule of ∀ we get a proof of `∃ (x : Y), g x = z` by applying `surj_g` to `z`. 
  cases h₁ with y hy, -- we use the elim rule of ∃ to get a term `y : Y` with the property `g y = z`
  have h₂, from surj_f y, -- by the elimination rule of ∀ we get a proof of `∃ (x : X), f x = z` by applying `surj_f` to `y`. 
  cases h₂ with x hx, -- we use the elim rule of ∃ to get a term `x : X` with the property `f x = y`
  rw ← hx at hy, -- we use the elim rule of ∃ 
  use x, -- we are trying to prove an ∃ statement 
  exact hy,
end


-- We can shorten the proof above by omiting `have` statements. 
example  (f : X → Y) (g : Y → Z)  (surj_f : is_surjective f) (surj_g : is_surjective g) : is_surjective (g ∘ f) :=
begin
  unfold is_surjective at *, -- We want to prove that `∀ (y : Z), ∃ (x : X), (g ∘ f) x = y` 
  intro z, -- We use the introduction rule of ∀ to fix `z : Z` and try to prove  `∃ (x : X), (g ∘ f) x = y` 
  cases surj_g z with y hy, 
  cases surj_f y with x hx,
  rw ← hx at hy, 
  use x, -- we are trying to prove an ∃ statement 
  exact hy,
end



def has_real_val_fun_ub {X : Type} (f : X → ℝ) :=
∃ a : ℝ, is_real_val_fun_ub f a 

def has_real_val_fun_lb {X : Type} (f : X → ℝ) :=
∃ a : ℝ, is_real_val_fun_lb f a 


#check has_real_val_fun_ub


def up_boundless {X : Type} (f : X → ℝ) := 
¬ has_real_val_fun_ub f

-- The following example says that the identity function is __boundless__:

example : up_boundless (λ x : ℝ, x) :=
begin
  sorry,
end

-- Challenge
def down_boundless {X : Type} (f : X → ℝ) := ¬ has_real_val_fun_lb f

example : 
down_boundless (λ x : ℝ, x) :=
begin 
  sorry,
end 

end PROOFS
