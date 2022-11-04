/-
Gaussian Integers
Sina Hazratpour
Adopted from Mathematics in Lean (by Avigad et al)
https://leanprover-community.github.io/mathematics_in_lean/06_Abstract_Algebra.html#building-the-gaussian-integers
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2022
-/

import ..prooflab
import .lec11_type_classes

import data.int.basic


namespace PROOFS
namespace STR


#check has_zero


class with_zero_str (X : Type) := (zero [] : X)

#check with_zero_str
#check with_zero_str ℕ


instance : with_zero_str ℕ := ⟨ nat.zero ⟩
instance : with_zero_str bool := ⟨ ff ⟩

#check @with_zero_str.zero

instance with_zero_product {A B : Type} [with_zero_str A] [with_zero_str B] :
  with_zero_str (A × B) :=
{
  zero := (with_zero_str.zero A, with_zero_str.zero B),
}


#eval with_zero_str.zero (bool × ℕ)


/-! Gaussian Integers -/

/-
https://en.wikipedia.org/wiki/Gaussian_integer
-/

@[ext]
structure gaussian_int :=
(re : ℤ)
(im : ℤ)

#check gaussian_int

notation ` ℤ[i] ` := gaussian_int


instance : has_repr ℤ[i] :=
{ repr := λ x,  repr x.re ++ "+" ++ "i" ++  repr x.im}



/- We prove some basic facts about Gaussian integers in the following namespace
-/
namespace gaussian_int

def zero : ℤ[i]  :=
{
  re := 0,
  im := 0,
}


#check zero -- ⟨0,0⟩


instance : has_zero ℤ[i]  := ⟨ ⟨0 ,0 ⟩  ⟩

instance : has_one ℤ[i]  :=  ⟨ ⟨1, 0⟩  ⟩


instance : has_mul ℤ[i]  := ⟨ λ x, λ y, ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩  ⟩

#eval (⟨1, 0⟩ : ℤ[i]) * ⟨0 , 1⟩
#eval (⟨1, 0⟩ : ℤ[i]) * ⟨0 , 2⟩
#eval (⟨1, 0⟩ : ℤ[i]) * ⟨0 , 3⟩

/-
0+i6
-/
#eval (⟨2, 0⟩ : ℤ[i]) * ⟨0 , 3⟩


instance : has_add ℤ[i]  := ⟨λ x y, ⟨x.re + y.re, x.im + y.im⟩⟩


#eval (⟨2, 0⟩ : ℤ[i]) + ⟨0 , 3⟩


instance : has_neg ℤ[i]  := ⟨ λ x , ⟨ - x.re, - x.im⟩  ⟩

#eval - (⟨2, 0⟩ : ℤ[i])

lemma zero_def :
  (0 : ℤ[i]) = ⟨0, 0⟩ :=
begin
  refl,
end


#check has_zero.zero

lemma one_def :
  (1 :ℤ[i]) = ⟨1, 0⟩ :=
begin
  refl,
end


@[simp]
lemma one_re_def :
  (1 :ℤ[i]).re = 1 :=
begin
  refl,
end


@[simp]
lemma one_im_def :
  (1 :ℤ[i]).im = 0 :=
begin
  refl,
end


theorem add_def (x y : ℤ[i]) :
  x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
begin
 refl,
end
theorem neg_def (x : ℤ[i]) :
  -x = ⟨-x.re, -x.im⟩ :=
begin
  refl,
end

theorem mul_def (x y : ℤ[i]) :
  x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
begin
  refl,
end


@[simp]
theorem add_re_def (x y : ℤ[i]) :
  (x + y).re = x.re + y.re :=
begin
  refl,
end

@[simp]
theorem add_im_def (x y : ℤ[i]) :
  (x + y).im = x.im + y.im :=
begin
  refl,
end


@[simp]
theorem mul_re_def (x y : ℤ[i]) :
  (x * y).re = x.re * y.re - x.im * y.im:=
begin
  refl,
end

@[simp]
theorem mul_im_def (x y : ℤ[i]) :
  (x * y).im = x.re * y.im + x.im * y.re:=
begin
  refl,
end


lemma add_assoc (x y z : ℤ[i]) :
  (x + y) + z = x + (y + z) :=
begin
   ext, -- By extensionality, we have to prove that the real part and the imaginary part of the two sides of the goal are equal. We reduce the problem to the problem of associativity of addition of integers.
   {repeat {rw add_re_def}, -- we took the real part of the sums separately and then we added them together,
    rw add_assoc,
   },
   -- {simp, rw add_assoc},-- to this end, we use
   --{rw add_def, unfold gaussian_int.im, rw add_assoc},
   {
    apply add_assoc,
   }
end


lemma mul_assoc (x y z : ℤ[i]) :
  (x * y) * z = x * (y * z) :=
begin
   ext, -- we are trying to show an equality of two instances of the structure `guassian_int`.
   repeat {rw mul_def},
   repeat {simp},
   {
    ring_nf, -- we proved this by using distributivity of mult over addition of integers which are all part of `ring` tactic.
   },
   {
    ring_nf, -- we proved this by using distributivity of mult over addition of integers which are all part of `ring` tactic.
   },
end


lemma mul_add_distrib (a b c : ℤ[i]) :
  a * (b + c) = a * b + a * c :=
begin
  ext,
  repeat{simp},  -- works because of the lemma `mul_re_def` and `add_def`
  repeat{ring_nf},
    --rw [mul_re_def, add_def],
end


lemma mul_add_distrib_alt (a b c : ℤ[i]) :
  a * (b + c) = a * b + a * c :=
begin
  ext,
  repeat{simp; ring_nf}, -- works because of the lemma `mul_re_def` and `add_def`
end


lemma add_mul_distrib (a b c : ℤ[i]) :
  (a + b) * c = a * c + b * c :=
begin
  ext,
  repeat{simp; ring_nf},
end



lemma add_comm (a b : ℤ[i]) :
   a + b = b + a :=
begin
  ext, --
  {
    repeat{rw add_re_def}, -- we want to reduce the addition of guassian integers to the addition of integers
    rw add_comm,
  },
  {
     repeat{rw add_im_def}, -- we want to reduce the addition of guassian integers to the addition of integers
    rw add_comm,
  },
end

lemma mul_comm (a b : ℤ[i]) :
  a * b = b * a :=
begin
  ext,
  { simp [mul_comm], },
  {simp [mul_comm], ring_nf, }
end


lemma add_zero (a : ℤ[i]) :
  a + 0 = a :=
begin
  ext,
  {
    simp,
    refl,
  },
  {
    apply add_zero,
  },
end


lemma zero_add (a : ℤ[i]) :
  0 + a = a :=
begin
  ext a,
  repeat {apply zero_add},
end



lemma mul_one (a : ℤ[i]) :
   a * 1 = a :=
begin
  ext a,
  --repeat {apply  mul_one},
  repeat {simp},
end


lemma one_mul (a : ℤ[i]) :
  1 * a = a :=
begin
  ext,
   repeat {simp},
end


end gaussian_int


#check add_semigroup

-- the structure of multiplicative semigroup
class mult_semigroup_str (S : Type) extends has_mul S :=
(mul_assoc : ∀ a b c : S, (a * b) * c = a * (b * c))

-- the structure of additive semigroup
class additive_semigroup_str (S : Type) extends has_add S :=
(add_assoc : ∀ a b c : S, (a + b) + c = a + (b + c))




instance : mult_semigroup_str ℕ :=
{
  -- mul := λ x, λ y, x * y,
  mul := has_mul.mul,
  mul_assoc := nat.mul_assoc,
}


instance : additive_semigroup_str ℕ :=
{
  add := λ x, λ y, x + y,
  add_assoc := nat.add_assoc,
}

#check 10 * 2
#check (10 : ℤ[i]) * 2
#eval (10 : ℤ[i]) * 2

#eval 10 * 2
#eval (⟨1,2⟩ : ℤ[i] ) * ⟨3,4⟩

instance : mult_semigroup_str ℤ[i]  :=
{
  mul := has_mul.mul, -- we retrieve the defintion of multiplication of ℤ[i] from the instance of the class `has_mul`.
  mul_assoc := by {intros x y z, rw gaussian_int.mul_assoc},
}






instance : additive_semigroup_str ℤ[i]  :=
{
  add := has_add.add,
  add_assoc := by {intros x y z, rw gaussian_int.add_assoc},
}





/- A __monoid__ is a type equipped with an associative binary operation and an identity element. -/

class mult_monoid_str  (M : Type) extends mult_semigroup_str M, has_one M :=
(mul_one :  ∀ a : M, a * 1 = a )
(one_mul : ∀ a : M, 1 * a = a )

class additive_monoid_str  (M : Type) extends additive_semigroup_str M, has_zero M :=
(add_zero :  ∀ a : M, a + 0 = a )
(zero_add : ∀ a : M, 0 + a = a )


def npower {M : Type} [mult_monoid_str M] : ℕ → M → M
  | 0 m := 1
  | (n + 1) m := m * (npower n m)


instance : mult_monoid_str ℤ[i]  :=
{
  mul_one :=  by { intro a, rw gaussian_int.mul_one, },
  one_mul :=  by { intro a, rw gaussian_int.one_mul, },
}

instance : additive_monoid_str ℤ[i] :=
{
  add_zero := by { intro a, rw gaussian_int.add_zero, },
  zero_add := by { intro a, rw gaussian_int.zero_add, },
}

/-
0+i2
-/

#eval npower 2 (⟨1, 1⟩ : ℤ[i])








end STR
end PROOFS
