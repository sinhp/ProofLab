/- 
Definitions, Lemmas, and Theorems.
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/
import ..prooflab
import lectures.lec0_intro

set_option pp.beta true
set_option pp.generalized_field_notation false
-- set_option pp.all true

/-
In this lesson, we learn how to define stuff in Lean. We also learn to state and use lemmas and theorems in Lean to prove some basic arithmetic equalities using the following additional tactics on top of the tactics `refl`, `exact`, `rw`, and `change`  of the previous lesson:

5. `calc` 
-/

namespace PROOFS

/-! ## Definitions, Lemmas, Theorems -/

section 
/- 
We can __define__ new stuff in Lean: A __definition__ assigns an expression to a keyword and puts it in the environment.
  def keyword : type := expression
In below, we define `foo` as the natural number `5`.  
-/   

def foo : nat := 5

#check foo
#print foo
#check foo + 7

/- 
We can similarly state a __lemma__ or a __theorem__. A lemma or a theorem is written the same way as `example` except that we give name to our lemmas and theorems for further use. 

- A genral __term style__ form of a `lemma` or a `theorem` is as follows: 

lemma name_of_lemma (context_of_our_assumptions) : 
  statement_of_lemma
:= proof_of_lemma

- A general form of a `lemma` in __tactic style__: 

lemma name_of_lemma (context_of_our_assumptions) : 
  statement_we_wanna_prove := 
begin 
  tactic_1 [...], 
  tactic_2 [...], 
  ⋮ 
  tactic_n [...], 
end 

For instance, in below, 
- `bar` is the __name_of_lemma__ which we can invoke later. 
- `(m n : ℤ)` is th __context__ of the lemma: these are the parameters which are used in the statement of the lemma. Think of context as a way of telling to Lean "let x, y, z, and n be natural numbers".
- `2 + n + m = n + 2 + m` is the __statement__ of the lemma: i.e. the thing we want to prove. The statement is usually a proposition which makes sense only in a given context. For instance, the contexts 
` m : ℕ `, and ` m n : ℕ ` would not work. Try! 
-/

lemma bar (m n : ℤ) : 
  2 + n - m = n + 2 - m := 
congr_arg (λ x, x - m) (add_comm 2 n) -- you do not need to understand this proof now

#check bar 

/- 
-`flt` is the __name_of_lemma__ which we can invoke later. 
- `(x y z n : ℕ)` is th __context__ of the lemma: 
- `n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n` is the __statement__ of the lemma:
-`sorry` is a way of telling Lean that we are going to supply a __proof__ later. 

-/
theorem flt (x y z n : ℕ) :
  n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n :=
sorry

theorem goldbach : ∀ n, 2 < n → n % 2 = 0 →
  ∃ p q : ℕ, p.prime ∧ q.prime ∧ n = p + q :=
sorry

/-
If we do not want to refer to the result we are proving we can simply declare it as `example`. It works the same way as theorem declaration, but without a name. 
-/
example : 
  2 + 3 = 5 := 
rfl

end --end of the section 



/-! ### Using definitions, lemmas, theorems -/

/-
We prove the lemma `bar` above, and we would like to use it to prove 
  `2 + n - 1 = n + 2 - 1` := 
which is a special case of `bar` when `m =1`. We do this by the expression `bar 1 n`. 
-/
example (n : ℤ) :
  2 + n - 1 = n + 2 - 1 := 
bar 1 n


#check eq.symm -- a lemma in lean library 
example (m n : ℕ) (e : m^2 = n) : 
  n = m^2 := 
begin
 exact (eq.symm e), -- here's how we use the lemma `eq.symm`. 
end

#check eq.subst
example (m n : ℕ) (h : n + 1 = 7) (e : m = n) : m + 1 = 7 := 
begin
 exact eq.subst (eq.symm e) h, 
end




-- try library_search before the last line
example (x y : ℕ) (h₁ : x = 0) (h₂ : y = 0) :
  x * y = 0 := 
begin
  rw h₁, -- we substitute `0` for `x` in the goal 
  rw h₂, -- we substitute `0` for `y` in the goal 
  exact zero_mul 0,
end 

-- another proof of the same statement
example (x y : ℕ) (h₁ : x = 0) (h₂ : y = 0) :
  x * y = 0 := 
begin
  rw h₁, 
  rw h₂, 
  exact mul_zero 0, -- `mul_zero` isntead of `zero_mul`. 
end 


example (x y z : ℕ)
  (h₁ : x + 0 = y) (h₂ : y = z) : x = z :=
begin
--  rw h, -- fails because rw works up to syntactic equality
  rw add_zero at h₁, -- would also work; note that the proof of `add_zero` is `refl`.
  rw h₁, -- now it works
  exact h₂, 
end



-- maybe seach_library or suggest? 
lemma add_sub_left (x y z : ℕ) : 
x + y - x = y := 
begin
rw add_comm, 
-- seach_library
-- suggest
exact nat.add_sub_cancel y x,
end 

#lint 

example (x y z : ℕ) : 
x + y - x = y := 
begin
rw add_comm, 
refine nat.add_sub_cancel _ _, -- use show_term to get the exact term
end 

/- 
In the following exercises, we will use the following two lemmas:
  ` mul_assoc a b c : a * b * c = a * (b * c) `
  ` mul_comm a b : a * b = b * a `

Hence the command 
  `rw mul_assoc a b c`,
will replace `a * b * c` by `a * (b * c)` in the current goal.

In order to replace backward, we use
  ` rw ← mul_assoc a b c`,
replacing `a * ( b * c )` by `a * b * c` in the current goal.
-/

example (a b c : ℝ) : 
  (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c,
end


example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ← mul_assoc a b c, 
  nth_rewrite 1 mul_comm, 
  rw mul_assoc, 
end

/-
Now let's return to the preceding example to experiment with what happens if we don't give arguments to `mul_assoc` or `mul_comm`. For instance, you can start the next proof with
  `rw ← mul_assoc`,
Try to figure out what happens.
-/

example (a b c : ℝ) : 
  a * (b * c) = b * (a * c) :=
begin
  rw ← mul_assoc,
  nth_rewrite 1 mul_comm,
  rw mul_assoc,
end

/- We can also perform _rewriting in an assumption_ of the local context, using for instance
  `rw mul_comm a b at h`,
in order to replace `a * b` by `b * a` in assumption `h`.

The next example will use a third lemma:
  `two_mul a : 2 * a = a + a`
-/

example (a b c d : ℝ) (h₁ : c = d * a + b) (h₂ : b = a * d) : c = 2 * a * d :=
begin
  rw h₂ at h₁,
  rw mul_comm at h₁,
  rw ← two_mul (a * d) at h₁,
  rw ← mul_assoc at h₁,
  exact h₁, 
end






/-! ### Tactic calc 
-- In the example below we use the lemma `mul_comm` (proved in mathlib/src/algebra/group/defs.lean). 
-/

#check mul_comm

example (a b c d : ℝ) (h₁ : c = d * a + b) (h₂ : b = a * d) : c = 2 * a * d :=
begin
  calc c = d * a + b   : by rw h₁ 
  ... = d * a + a * d  : by rw h₂ 
  ... = a * d + a * d  : by rw mul_comm d a 
  ... = 2 * (a * d)    : by rw two_mul 
  ... = 2 * a * d      : by rw mul_assoc,
end

-- Warning: Be careful to put exactly _three_ dots (...); otherwise you get an incomprehensile error. 

/-
Use the following lemmas to prove the so-called "difference of two squares" identity 
-/ 

section 
variables a b c x : ℝ
#check (pow_two x : x^2 = x * x)
#check (mul_sub a b c : a * (b - c) = a * b - a * c)
#check (add_mul a b c : (a + b) * c = a * c + b * c)
#check (add_sub a b c : a + (b - c) = (a + b) - c)
#check (sub_sub a b c : a - b - c = a - (b + c))
#check (add_zero a : a + 0 = a)
end 

-- Difference of two squares
lemma diff_of_squares_real (a b : ℝ) : 
  (a + b) * (a - b) = a^2 - b^2 :=
begin
  calc   (a + b) * (a - b) = (a + b) * a - (a + b) * b : by rw mul_sub (a + b) a b 
  ... =  (a * a + b * a) - (a * b + b * b)            : by rw [add_mul a b a, add_mul a b b]  
  ... =  (a^2 + b * a) - (a * b + b^2)                : by rw [pow_two a, pow_two b]
  ... =  a^2 + b * a - a * b - b^2                    : by rw [sub_sub _ _ _ ] 
  ... =  a^2 + (b * a - a * b) - b^2                  : by rw [add_sub _ _ _]
  ... =  a^2 - b^2                                    : by rw [mul_comm b a, sub_self,add_zero],
end

lemma prod_distrib_sum_binomial₁ (x y : ℝ) :  
  (x + y) * (x * x + 2 * (x * y) + y * y) = x * x * x + 3 * x * x * y + 3 * x * y * y + y * y * y := 
begin
  sorry
end   






end PROOFS