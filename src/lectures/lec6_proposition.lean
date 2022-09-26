/- 
Logic of Propositions 
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/



/- # New tactics unveiled in this lesson:
12. `split` (for introduction of `∧`)
13. `cases` (for elimination of `∧`)
14. `assumption` (for using a proof from context of assumptions)
15. `intro` (for introduction of `→`)
16. `apply` (for backward elimination of `→`)
17. `have` (for introducing auxiliary intermediate goals)
18. `left` (for introduction of `∨`)
19. `right` (for introduction of `∨`)
20. `suffices`
-/



/- # Goals of this lecture: 
1. Identify techniques for proving a proposition based on its logical structure.
2. Recognize and apply standard proof techniques, including proof by negation, proof by contraposition, and proof by contradiction. 
3. Learn to simplify your proofs.
4. Do all of the above using interactive Lean tactics.  
-/


import ..prooflab
--import .arithmetic_with_tactics
import .lec5_function_composition -- importing is transitive, hence we have already imported proofs1 and proofs0.

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true

namespace PROOFS



/-! ## Propositions 
Reminder: We declare a proposition by `P : Prop`. 
For `P : Prop`, we read `hp : P` as "hp is a proof of P", or "the hypothesis P verified by hp". 
-/

/-
We introduce global variables; in below P and Q are accessible throughout the entire file, and any file which imports this file.
-/
variables P Q R : Prop -- let `P`, `Q` and `R` be propositions. 


/- 
Lean's "check" command tells us 
the type of the object we have constructd. 
-/
#check P 
#check P ∧ Q -- conjunction 
#check P ∨ Q -- disjunction 
#check P → Q -- implication 
#check ¬ P -- negation 


/-! ## New Propositions from the Old 

Using simple (aka __atomic__) propositions such as “The sun is shining” and “It is raining” we can form the more complicated proposition “The sun is shining and It is raining”.

That required us to first unquote the sentences, insert an “and” and then put a quote around the resulting sentence.

In this way, we can make new propositions from old propositions using __connectives__ (such as “and”/conjunction, "if ... then"/implication, "or"/disjunction). For each connective, we specify a __rule__ to __introduce__ a proof of the compound proposition using that connective (the so-called introduction rule) and a rule to __use__ or ___eliminate__ such a proof.

We call a compound proposition (such as “The sun is shining and It is raining”) a __propositional formula__. 
-/


/-! ### Conjunction (and) 
We use the tactic __split__ in order to prove a proposition formula of the form `P ∧ Q`. 

We use the tactic __cases__ in order to use a proof of `P ∧ Q` to prove some other proposition. The tactic `cases` replaces `h : P ∧ Q` by a pair of assumptions, `hp : P` and `hq : Q`. 
-/

-- introduction example 
example (hp : P) : P ∧ P := 
begin
  split, 
  { 
    -- the proof of the first subgoal which is `P` 
    exact hp, 
  },
  {
    -- the proof of the second subgoal which is `P` 
    exact hp, 
  },
end 




example (hp : P) : P ∧ P := 
begin
  split, 
  repeat {exact hp},
end 




-- elimination example 
lemma fst_prop (h : P ∧ Q) : 
  P := 
begin 
  cases h,  
  exact h_left, 
end 




-- elimination example 
lemma fst_prop_alt (h : P ∧ Q) : 
  P := 
begin 
  cases h with h₁ h₂,  
  exact h₁,  
end 



--elimination example 
lemma snd_prop (h : P ∧ Q) : 
  Q := 
begin 
  cases h with h₁ h₂,  
  exact h₂,  
end 





/- the following is an example of both intro and elim rules: we need intro rule to construct a proof of `Q ∧ P` and we need elim rule to be able to use `h : P ∧ Q` -/
lemma conjunction_swap (h : P ∧ Q) : 
  Q ∧ P := 
begin
  split, 
  {
    -- we need to prove `Q`. 
    -- we are trying to use `h` to prove `Q` holds. 
    cases h with sheep goat,
    exact goat, 
  },
  {
   -- we need to prove `P`. 
    -- we are trying to use `h` to prove `Q` holds. 
    cases h with sheep goat,
    exact sheep,  
  }, 
end   


#check conjunction_swap



lemma conjunction_swap_alt (h : P ∧ Q) : 
  Q ∧ P := 
begin
  cases h with hp hq, -- eliminating h to get proofs of `P` and `Q`. 
  split,  -- we want to introduce a proof of conjunction 
  {
    exact hq, 
  },
  {
    exact hp, 
  },
end   



------------------------
-- tactic __assumption__ 
------------------------
/-
The `assumption` tactic looks through the assumptions in the context of the current goal, and if there is one matching the conclusion, it applies that asssumption. Here is an example:
-/

/- 
This one is the same as the last proof but more parsimonous: we use `repeat {assumption}` instead of many instances of `exact`.  
-/


lemma conjunction_swap_alt_alt (h : P ∧ Q) : 
  Q ∧ P := 
begin
  cases h with hp hq, -- eliminating h to get proofs of `P` and `Q`. 
  split, 
  {
    assumption, -- this tactic means you are instructing Lean to go and find the proof of the goal from the context of assumption, only if the exact proof exists in the context. 
  },
  {
    assumption, 
  },
end   



lemma conjunction_swap_alt_alt_alt (h : P ∧ Q) : 
  Q ∧ P := 
begin
  cases h with hp hq, -- eliminating h to get proofs of `P` and `Q`. 
  split, 
  repeat {assumption}, 
end   


lemma conjunction_swap_alt_alt_alt_alt (h : P ∧ Q) : 
  Q ∧ P := 
begin
  split, 
  repeat { cases h, assumption}, 
end   




-- introduction example : complete the proof below using only `assumption` and `exact` tactics. 
example (hp : P) (hq : Q) (hr : R) : 
  (P ∧ Q) ∧ (P ∧ R) :=
begin
  split, 
  {
    split, 
    {
      assumption, -- or exact hp
    },
    {
      assumption, 
    },
  },
  {
    split, 
    {
      assumption,
    },
    {
      assumption,
    },
  },
end 


-- Challenge: make it shorter with `repeat`. 






example (hp : P) (hq : Q) (hr : R) : 
  (P ∧ Q) ∧ (P ∧ R) :=
begin
  split, 
  {
    split, 
      repeat {assumption},
  },
  {
    split, 
    repeat {assumption},
  },
end 







/-! ### Implication (If ... then ...) 
The implication `P → Q` is a new proposition built from P and Q and we read it as “if P then Q”.

Implicaiton __introduction__:
If under the assumption that `P` is true we can derive that `Q` is true, then we know that `P → Q` is true. Note that, in this process, we actually do not know whether P is true or not; all we know is that in case `P` holds, then so does `Q`. To assume `P` first we introduce a hypothetical proof `hp` of `P`, and we use `hp` to construct a proof of `Q`, and thereby show that `Q` holds under the assumption that `P` holds. 

Implication __elimination__: 
Application of a proof 
`h : P → Q`
to a proof 
`p : P`  
is achieved by the expression
`h p`  
that is `h` followed by `p`.

This is (like) function application.

If `h` and `p` are compound expressions, we put brackets around them to make it clear where each one begins and ends. 
e.g. `h₁ h₂ h₃` is interpreted by Lean as `(h₁ h₂) h₃`.
-/


--introduction example
example : 
  P → P := 
begin 
  intro hp, -- this is the assumption that `P` holds. our goal changes 
  exact hp, 
end 

example : 
false → false := 
begin 
  intro hp, 
  exact hp, 
end 


--introduction example
lemma conjunction_commutative :
  P ∧ Q → Q ∧ P := 
begin
  intro h, 
  cases h,
  split, 
  {exact h_right},
  {exact h_left}, 
end   

--Alternatively, we can use the lemma `conjunction_swap` which we proved before: 
example : 
  P ∧ Q → Q ∧ P := 
begin
  intro h, 
  exact (conjunction_swap P Q h), 
end 


/- Next examples constructs a proof of `(0 = 1) → (0 = n)`. -/

lemma nat_mul_congr (x y z : ℕ) (h : x = y) : 
  x * z = y * z := 
begin
sorry, 
end 
 
-- #check nat_mul_congr


-- introduction example
example (n : ℕ) : 
  (0 = 1) → (0 = n) := 
begin
  intro h₁, 
  -- now under the hypothetical assumption that `0 = 1` we need to prove that `0 = n`.  
  sorry, 
end 




--introduction example
lemma conjunction_commutative_alt :
  P ∧ Q → Q ∧ P := 
begin
  sorry, 
end   





--Alternatively, we can use the lemma `conjunction_swap` which we proved before: 
example : 
  P ∧ Q → Q ∧ P := 
begin
  sorry,  
end 





example : 
  P → Q → P :=
begin
sorry,
end 




example : 
  P → Q → P ∧ Q :=
begin
  sorry, 
end 






-- elimination exmaple: applicaiton
lemma modus_ponens : 
  P → (P → Q) → Q := 
begin   
  intros hp h, 
  exact h hp,
end 





-- dependent application/evaluation
lemma dep_modus_ponens: 
  P → (P → P → Q) → Q :=
begin
  sorry, 
end 

example : 
  P → (P → P → Q) → Q :=
begin
  sorry, 
end 

/-
Transitivity of implications: If we know that  proposition P implies Q and Q implies R then we know that  P implies R. 
-/

theorem transitivity_of_implication_1 :
  (P → Q) → (Q → R) → P → R :=
begin
  sorry, 
end   

/-
Another style to write the same proof above by using the tactic 
have ..., from ...
-/

theorem transitivity_of_implication_2 :
  (P → Q) → (Q → R) → P → R :=
begin   
  sorry, 
end 

example : 
  (P → (Q → R)) → (P ∧ Q → R) :=
begin 
  sorry, 
end 


------------------------
-- tactic __apply__ 
------------------------
/- The `apply` tactic takes a proof of a general statement or implication, tries to match the conclusion with the current goal, and leaves the hypotheses, if any, as new goals. If the given proof matches the goal exactly (modulo definitional equality), you can use the exact tactic instead of apply. -/

example (hpq : P → Q) (hqr : Q → R) (hp : P) : 
  R :=
-- We prove `R` using backward reasoning as follows.  
begin
-- To prove `R`, by hypothesis `hqr` it suffices to prove `Q`.
  apply hqr,
-- To prove `Q`, by hypothesis `hpq` it suffices to prove `P`.  
  apply hpq,
-- To prove `P` we use hypothesis `hp`. 
  apply hp,
end


section 
variables a b c : ℝ
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
end 

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) :
  x ≤ z := 
begin
-- our goal is to prove `x ≤ z`. After using `apply le_trans` Lean is searching the context to find some `y` with `x ≤ y` and `y ≤ z` so that it can apply `le_trans` to them. 
  sorry,
-- the goals are ⊢ x ≤ ?m_1 and ?m_1 ≤ z : We solve the first goal using `h₀`. One `h₀` is supplied, `?m_1` is replaced by `y`. 
  sorry, 
-- ⊢ the only remaining goal is  `y ≤ z`. 
  sorry,
-- alternatively, we could have used `exact h₁` as usual.   
end


/- 
let's do curry fully tactic style; we use our new tactic `apply`.
-/
lemma curry_prop : 
  (P ∧ Q → R) → (P → Q → R) :=
begin 
  sorry, 
end 

#check curry_prop
#check curry 


lemma curry_prop_fun : 
  (P ∧ Q → R) → (P → Q → R) :=
λ h, λ hp, λ hq, h ⟨hp, hq⟩   

#check curry_prop_fun



example : 
  (P → (Q → R)) → (P ∧ Q → R) :=
begin 
  sorry, 
end 



/-
The proof below shows us why we prefer backward reasoning with `apply`. A forward reasoning proof would be more complicated 
-/

example : (((P → Q)  → Q) → Q) → P → Q :=
begin 
  sorry, 
end








end PROOFS 