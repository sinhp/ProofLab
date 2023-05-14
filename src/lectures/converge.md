/-! ## Question 7 (30 pts) 
A sequence `a` in `ℝ` __converges__ to a point `t : ℝ` if for any positive `ε` the values of the sequence are eventually in the open interval `(t - ε, t + ε)`.  The point `t` is said to be a __limit__ of `a`. 
-/ 

structure converges (a : ℕ → ℝ) := 
(limit : ℝ) 
(conv_condition : ∀ ε > 0, ∃ b : ℕ, ∀ n : ℕ, b ≤ n → | a n - limit | < ε)


#check converges

