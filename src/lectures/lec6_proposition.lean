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

    P   Q
   -------- ∧-intro
    P ∧ Q 

We use the tactic __cases__ in order to use a proof of `P ∧ Q` to prove some other proposition. The tactic `cases` replaces `h : P ∧ Q` by a pair of assumptions, `hp : P` and `hq : Q`. 

    P ∧ Q
   -------- ∧-elim_left
      P 

    P ∧ Q
   -------- ∧-elim_right
      Q 


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

    P
    .
    .
    .
    Q
--------- (→ intro)
  P → Q


Implication __elimination__: 
Application of a proof 
`h : P → Q`
to a proof 
`p : P`  
is achieved by the expression
`h p`  
that is `h` followed by `p`.

This is (like) function application.


  P → Q   P 
------------- (→ elim)
      Q



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


example : 
  false → true := 
begin
-- an example of this is the proposition (0 = 1) → (1 = 1)
intro hp, 
exact trivial, -- trivial is the unique proof of proposition `true`, therefore `true` is true. 
end 


--introduction example
lemma conjunction_commutative :
  P ∧ Q → Q ∧ P := 
begin
  intro hpq, 
  -- we want to use the elim rule of conjunction (`∧`) to construct a proof of `P` and a proof of `Q` to use them later. 
  cases hpq with hp hq,
  -- we want to use the intro rule of conjunction to prove our goal `Q ∧ P` 
  split,
  {
    -- well, we know that `Q` is true and the proof of that is `hq`. 
    exact hq,
  },
  {-- well, we know that `P` is true and the proof of that is `hp`. 
    assumption, -- note that `hp` was introduced later in the proof
  },
end   




--Alternatively, we can use the lemma `conjunction_swap` which we proved before: 
example : 
  P ∧ Q → Q ∧ P := 
begin
-- the second line of the following proof uses the elimination rule of implication which we have not learned yet, but we will in about five minutes.  
  intro hpq, 
  exact conjunction_swap P Q hpq, 
end 



 -- an example of implication introduction 
example (n : ℕ) : 
  (0 = 1) → (0 = n) := 
begin 
intro h₁, 
calc 0 = 0 * n : by rw zero_mul
... = 1 * n : by rw h₁
... = n : by rw one_mul,
end 



/- Next examples constructs a proof of `(0 = 1) → (0 = n)`. -/

lemma nat_mul_congr (x y z : ℕ) (h : x = y) : 
  x * z = y * z := 
begin
  rw h,
end 
 


-- #check nat_mul_congr

------------------------
-- tactic __have__ 
------------------------

/- `have` is a good tactic to use, if you want to add a new intermediate subgoal which, after proving it, can be used later as a new assumption in the (updated) context. 

There are two styles of using the tactic `have`.

- The term-style: 
` have hp : P, from ...  `


- The tactic-style: 
` have hp : P, by {tactic_1 ..., tactic_2 ...,  tactic_n ... } `

In the first style, we are introducing a new assumption `hp` (a proof of proposition `P`) from another proof (`...`) that we know how to construct.   
-/



example (n : ℕ) : 
  (0 = 1) → (0 = n) := 
begin
  -- we want to prove an implication, hence we use the implication introduction rule. 
  intro h₁, 
  -- under the hypothetical assumption that `0 = 1` we need to prove that `0 = n`.  To prove this we use the lemma `nat_mul_congr` in the following way: we use the lemma by using x to be `0` and `y` to be `1` and `z` to be `n` 
  -- We use the tactic `have` to add a new assumption `h₂` which proves that `0 * n = 1 * n` from the lemma `nat_mul_congr` applied to arguments `0 1 n h₁`. 
  have h₂ : 0 * n = 1 * n, from nat_mul_congr 0 1 n h₁, 
  -- this proves ` 0 * n = 1 * n` 
  -- use h₂ to prove `0 =n` 
  rw [zero_mul, one_mul] at h₂, 
  assumption,
end 



example (n : ℕ) : 
  (0 = 1) → (0 = n) := 
begin
  intro h₁, 
  -- now under the hypothetical assumption that `0 = 1` we need to prove that `0 = n`.  
  have h₂ : 0 * n = 1 * n, from nat_mul_congr 0 1 n h₁, 
  -- we add a new assumption that `0 = 0 * n` using the tactic-style `have` and the lemma `zero_lemma`. 
  have h₃ : 0 = 0 * n, by {rw zero_mul}, 
  -- we add a new assumption that `n = 1 * n` using the tactic-style `have` and the lemma `one_mul`. 
  have h₄ : n = 1 * n, by {rw one_mul}, 
  rw ← h₃ at h₂,  
  rw ← h₄ at h₂,  
  show 0 = n, from h₂, 
end 



example (n : ℕ) : 
  (0 = 1) → (0 = n) := 
begin
  intro h, 
  simp at *, 
  exfalso, 
  assumption,
end 







--Alternatively, we can use the lemma `conjunction_swap` which we proved before: 
example : 
  P ∧ Q → Q ∧ P := 
begin
  intro h₁, 
  exact conjunction_swap P Q h₁, 
end 





example : 
  P → Q → P :=
begin
-- we want to prove `P → (Q → P)` so we use the intro rule of `→`
intro h₁, 
-- we are proving an implication, hence we use the intro rule of → 
intro h₂, 
-- we know `P` is true by `h₁`. 
assumption,
end 




example : 
  P → Q → P ∧ Q :=
begin
  sorry, 
end 





-- Application elimination exmaple aka Modus Ponens
lemma modus_ponens : 
  P → (P → Q) → Q := 
begin   
  intros hp h, 
  exact h hp,
end 



-- Depenedent Modus Ponens
lemma dep_modus_ponens: 
  P → (P → P → Q) → Q :=
begin
  -- we want to prove P → ((P →(P → Q)) → Q) so we use intro rule of → 
  intro h₁, 
  -- we want to prove (P →(P → Q))  → Q so we use intro rule of → 
  intro h₂, 
  --  we want to Q; we create a new subgoal P → Q, and prove it using tactic `have`
  have h₃ : P → Q, from h₂ h₁, 
-- we use `h₃` to prove `Q` by application elimination. 
  exact h₃ h₁, 
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
exact le_trans h₀ h₁,
end 


example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) :
  x ≤ z := 
begin
-- our goal is to prove `x ≤ z`. After using `apply le_trans` Lean is searching the context to find some `y` with `x ≤ y` and `y ≤ z` so that it can apply `le_trans` to them. 
  apply le_trans,
-- the goals are ⊢ x ≤ ?m_1 and ?m_1 ≤ z : We solve the first goal using `h₀`. One `h₀` is supplied, `?m_1` is replaced by `y`. 
  apply h₀,
-- ⊢ the only remaining goal is  `y ≤ z`. 
  apply h₁,
-- alternatively, we could have used `exact h₁` as usual.   
end



/- 
let's do curry fully tactic style; we use our new tactic `apply`.
-/
-- a tautology is proposition which is always true. 
lemma curry_prop : 
  (P ∧ Q → R) → (P → Q → R) :=
begin 
  intro h₁, -- we want to prove the implication (P ∧ Q → R) → (P → Q → R) hence we use the introduction rule of implication. 
  intro h₂, -- we want to prove the implication P → (Q → R), hence we use the introduction rule of implication. 
  intro h₃,  -- we want to prove Q → R, hence we use the introduction rule of implication. 
  apply h₁, -- we want to show R hence by backward proving we need to supply a proof of P ∧ Q
  split, -- we want to prove P ∧ Q and therefore we use the introduction rule of conjunction 
  repeat {assumption},
end 


example : 
  (P ∧ Q → R) → (P → Q → R) :=
begin
itauto,
end   


example : 
  (P ∧ Q → R) → (P → Q → R) :=
begin
itauto,
end   



example : 
  (P ∧ Q → R) → (P → Q → R) :=
begin
exact and_imp.mp,
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







/-! ### Falsity
Sometimes we need to work with propositions which are always false such as “A bachelor is married”, or "0 = 1". In Lean, we denote the false proposition by `false`. The universal property of a false proposition is that any other proposition follows from the false proposition. We can prove any proposition from `false`. This is known as the __principle of explosion__ 🎆 aka ex falso. 
-/

example (P : Prop) (h : false) :
  P :=
begin
  exfalso, 
  exact h, 
end   
 
example : 
  false → P := 
begin
  intro h,  
  exfalso,
  exact h, 
end


/-! ### True
Sometimes we need to work with propositions which are always true such as “A bachelor is unmarried”, or "0 = 0". In Lean, we denote the false proposition by `true`. The universal property of a false proposition is that any other proposition entails the true proposition. In fact, `true` has a unique proof, namely `trivial`.  
We can prove any proposition from `false`. This is known as the __principle of explosion__ 🎆 aka ex falso. 
-/

example : 
  true := 
begin
  exact trivial,
end   

example : false → true → Q → P → Q   :=
begin 
intro u, 
exfalso,
exact u, 
end






/-! ### Negation  
If we start with a propositon `P`, the negation `¬P` (aka "not P") is _defined_ by the formula `P → false`, which you can think of as saying that `P` implies something impossible (`false`). Therefore, if `¬ P` is the case, then `P` cannot be the case, since if `P` were the case, we would conclude that something false/impossible would be the case. The rules for negation are therefore similar to the rules for implication. To prove/introduce `¬P`, assume `P` and derive a contradiction `false` (i.e. construct a proof of proposition `false`).  An example of this is the proof of irrationality of root 2.
To eliminate `¬P`, given a proof of `P` and a proof of `¬ P` we get `false`. 
-/

-- We are trying to prove that "if P then if not P then false"
example : 
  P → ¬P → false := 
begin 
  intro hp, -- we want to prove the implication P → (¬P → false), therefore we use implication introduction
  intro hnp, -- we want to prove the implication (¬P) → false, therefore we use implication introduction 
  apply hnp,          -- we have a proof of ¬P, so we use the elimination for negation to construct a proof of false.
  assumption,
end  






example : P → ¬P → false := 
begin 
intro hp, 
intro hnp, 
exact hnp hp, -- the direct form of implication elimination
end  





lemma not_imply : 
  (P ∧ ¬ Q) → ¬ (P → Q) := 
begin
  intro hpnq, -- we are trying to prove the implication (P ∧ ¬ Q) → (¬ (P → Q))
  -- we want to prove  the negation ¬ (P → Q), so we use the intro rule for negation 
  intro hpq, 
  cases hpnq with hp hnq,-- we eliminate the conjunction 
  apply hnq, -- we use the elim rule for `¬ Q` to change the goal from false to Q
  apply hpq, --we use the elim rule for `P → Q` after which we just need to prove `P`.  
  assumption, 
end   



lemma proof_by_contrapositive 
  (P Q : Prop) : (P → Q) → (¬Q → ¬P) := 
begin 
  intro hpq, 
  intro hnq,
  intro hp,
  apply hnq, 
  apply hpq,
  assumption,
end 






-- Tactic __suffices__:
lemma proof_by_contrapositive_alt
(P Q : Prop) : (P → Q) → (¬Q → ¬P) := 
begin
  intro hpq, 
  intro hnq, 
  intro hp, 
  suffices hq : Q, from hnq hq, -- this is very much like apply; it changes the goal to the assumption of the implication. It says I only need to prove Q becasue once i do that i can use `hnq` 
  apply hpq, 
  exact hp,
end 

-- Another example of `suffices`
example : 
  P → (Q ∧ R) → P ∧ Q := 
begin
  intros h₁ h₂ , 
  suffices h₃ : Q, from ⟨h₁,h₃⟩,
  exact h₂.1,
end 




-- Tactic __exfalso__:
example : 
  P ∧ ¬ P → Q :=
begin
  intro hpnp, -- we want to prove the implication (P ∧ ¬ P) → Q, so we use the intro rule of implication
  cases hpnp with hp hnp, 
  exfalso, -- is a tactic for the backward elimination of `false`. This means from a proof of `false` everything followes. 
  exact hnp hp,
end





example : 
  P ∧ ¬ P → Q :=
begin
  intro hpnp, -- we want to prove the implication (P ∧ ¬ P) → Q, so we use the intro rule of implication
  cases hpnp with hp hnp, 
  have f : false, from hnp hp, 
  exfalso, -- is a tactic for the backward elimination of `false`. This means from a proof of `false` everything followes. 
  assumption,
end



example : 
  P ∧ ¬ P → Q := 
begin
  intro hpnp,
  exfalso, 
  sorry, 
end 


/- 
A __contradiction__ is a collection of propositions which together lead an absuridty, i.e. a proof of `false`. For instance if we have a proof of a proposition `P` and a proof of `¬ P` then we can prove `false`. Hence `¬ P` contradicts `P`. 

Tactic __contradiction__: The `contradiction` tactic searches for a contradiction among the hypotheses of the current goal. 
-/

example : 
  P ∧ ¬ P → Q :=
begin
  intro h, 
  cases h, 
  contradiction,
end








/-! ### Disjunction (or) 
- Tactic for disjunction introduction:  We use the tactic __left__ or __right__ in order to prove a propositional formula of the form `P ∨ Q`. 


      P
   -------- ∨-intro-left 
    P ∨ Q
 


      Q
   -------- ∨-intro-right
     P ∨ Q


 
- Tactic for disjunction elimination: We use the tactic __cases__ in order to use a proof of `P ∨ Q` to prove some other proposition. 



  P ∨ Q     P        Q
            .        .
            .        .
            .        . 
            R        R
----------------------------
            R

-/



example (hp : P) : 
  P ∨ Q ∨ ¬ P :=
begin
  left,
  assumption,
end 





example (hq : Q) : 
  P ∨ Q ∨ ¬ P :=
begin
  right, 
  left, 
  assumption,
end


example (hq : Q) : 
  P ∨ Q ∨ ¬ P :=
begin
  itauto,
end


-- Challenge: fill in the `sorry` below. 
-- introduction example
example (h : P ∧ Q) : 
  P ∨ Q :=
begin
  sorry, 
end 



-- elimination example 
lemma or_swap (h :  P ∨ Q) :
  Q ∨ P :=
begin
  sorry, 
end 

/-
The tactic `cases` can be used like `cases h with hp hq` to give customary name to the branches of a disjunction, using `hp` for the first branch and `hq` for the second. 
-/

example : P ∨ Q → Q ∨ P :=
begin
  sorry, 
end



theorem conjunction_distrib_disjunction (h : P ∧ (Q ∨ R) ) : 
  (P ∧ Q) ∨ (P ∧ R) :=
begin
   cases h, -- eliminate ∧ in P ∧ (Q ∨ R)
   cases h_right, -- eliminate ∨ in Q ∨ R
     sorry, 
end



lemma mul_eq_zero_of_eq_zero_or_eq_zero (a b : ℝ) (h : a = 0 ∨ b = 0) : 
  a * b = 0 := 
begin
  sorry, 
end   

#check eq_zero_or_eq_zero_of_mul_eq_zero

example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  sorry, 
end


end PROOFS