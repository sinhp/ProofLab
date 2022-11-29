/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------

# Structures (bundled)
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import .lec7_predicate



namespace PROOFS 


namespace STR  --nested inside the namespace PROOFS

variables {X Y Z : Type}
variable {f : X → Y}




/-! ## Some Simple Structures -/

-- The structure of RGB colors 

-- every RGB color has a "red" component, a "green" component, and a "blue" component. Therefore, we have three fields `red`, `green` and `blue` in the structure `rgb`. 
-- https://en.wikipedia.org/wiki/RGB_color_model#/media/File:RGB_combination_on_wall.png


structure rgb :=
(red green blue : ℕ)


-- For instance JHU Heritage Blue is R0 G45 B114 
-- first we give the type of the structure instance and then the value of the instance
-- `JHU_Heritage_Blue` is an instance specified by the value `⟨0, 45, 114⟩`



/-! ### Instances of Structures -/

def JHU_Heritage_Blue : 
  rgb := ⟨0, 45, 114⟩ 

#print JHU_Heritage_Blue -- the command to access the previously defined instances of structures. 


-- We have three __projections__ to get access to the fields of rgb
#check rgb.red -- this is a function which maps a tuple of `rgb` to the value of its `red` component.
#check rgb.green
#check rgb.blue

#check JHU_Heritage_Blue.red -- this is the value of applying `rgb.red` to `JHU_Heritage_Blue`. `JHU_Heritage_Blue.red` is a shorthand notation for `rgb.red JHU_Heritage_Blue`. 

#eval JHU_Heritage_Blue.red
#eval JHU_Heritage_Blue.green
#eval rgb.green JHU_Heritage_Blue



/-! ### Defining Functions on Structures -/

def shuffle (c : rgb) : rgb := -- we have to give the components of `shuffle c`. 
{ red   := rgb.green c,
  green := rgb.blue c,
  blue  := rgb.red c }


def shuffle_alt (c : rgb) : rgb := -- we have to give the components of `shuffle c`. 
{ red   := c.green,
  green := c.blue,
  blue  := c.red }  


#reduce shuffle (JHU_Heritage_Blue)
#reduce shuffle (shuffle (JHU_Heritage_Blue))
-- https://g.co/kgs/mvHSbz

#reduce shuffle(shuffle (shuffle (JHU_Heritage_Blue)))



lemma three_shuffle_is_nil :
  shuffle ∘ shuffle ∘ shuffle = id :=
begin 
  funext c, -- we want to prove for any arbitray `x : rgb` the application of LHS and the RHS to `x` are the same. 
  dsimp, -- definitionally simplify both sides 
  cases c, -- to prove two colors are the same we have to prove they have equal components. 
  refl, 
end



@[ext] 
structure R1 := (x : ℝ)  

def folding : ℝ → R1 := 
λ a, 

@[ext] 
structure R2 := (x : ℝ) (y : ℝ)

@[ext] -- this is used to prove two instances of R3 are the same by proving their components are the same.
structure R3 := (x : ℝ) (y : ℝ) (z : ℝ)


/- 
The @[ext] annotation tells Lean to automatically generate theorems that can be used to __prove that two instances of a structure are equal when each of their components are equal__, a property known as __extensionality__.  Therefore, if a theorem involves a concept defined by an @[ext] annotation, we can use tactic `ext` to reduce an equation between two elements of the structure to equations between the components.
-/ 


--three projection 
#check R3.x 
#check R3.y
#check R3.z





/-! ### Equality of Instances of Structures -/

example (a b : R3) (h : a = b)  : 
  (a.x = b.x) :=
begin
  exact congr_arg R3.x h,
end 



example (a b : R3) (h : a = b)  : 
  (a.x = b.x) :=
begin
  cases a, -- reduces `a` to its components 
  cases b, -- reduces `b` to its components 
  dsimp, 
  cases h, -- we don't undertand this because equality is an inductive type in a way which is too advanced for us now. 
  refl, 
end   


-- Challenge: fill in the `sorry` 
example (a b : R3) : 
  a = b ↔ (a.x = b.x) ∧ (a.y = b.y) ∧ (a.z = b.z) :=
begin
  split,
  intro h, 
  {
    split, 
    {
      exact congr_arg R3.x h,
    },
    {
      split, 
      {
        sorry,
      },
      {
        sorry, 
      },
    },
  },
  {
    intro h, 
    obtain ⟨h₁, h₂, h₃⟩ := h,
    ext,
    assumption',
  },
end 


/- 
We can define points by specifying their coordinates. Lean provides multiple ways of doing that.
-/

section some_affine_points
-- the first way: 

def Pt_0 : R1 := 
{
  x := 0,
} 

def vect_a (a: ℝ)  : R1 := 
{
  x:= a,
}

#reduce vect_a -- takes r : ℝ to <r>
#check vect_a 2 -- 

def Pt_0p1 : R2 :=
{ 
  x := 0,
  y := 1, 
}

def Pt_0p1_alt  : R2 := 
⟨0 , 1⟩ 


#check Pt_0p1 -- an instance of R2 which is to say a point on the 2-dim plane 


def Pt_0n1 : R2 :=
{ 
  x := 0,
  y := -1 
}

def Pt_n1p1n1 : R3 :=
{ 
  x := -1,
  y := 1,
  z := -1 
}

def Pt_p1n1p1 : R3 :=
{ 
  x := 1,
  y := -1,
  z := 1 
}

end some_affine_points


/-! ### Functions between structures -/


/-!  #### Projections 
Projections π_i : ℝⁿ → ℝ, for 1 ≤ i ≤ n, are functions defined by the assignment  
π_i (x_1, … ,x_n) = x_i 
The i-th projection picks the i-th coordinate and forgets the rest of the coordinates. 
-/

def R2.proj₁ (a : R2) : R1 := 
⟨ a.x ⟩ 

def R2.proj₂ (a : R2) : R1 := 
⟨ a.y ⟩

--Challenge: define all of the projections `R3 → R1`

def R3.proj₁ (a : R3) : R1 := ⟨ a.x ⟩  
def R3.proj₂ (a : R3) : R1 := ⟨ a.y ⟩ 
def R3.proj₃ (a : R3) : R1 := ⟨ a.z ⟩ 

def sum_of_components (a : R3) : ℝ := 
a.x + a.y + a.z 

#check sum_of_components

#eval sum_of_components Pt_n1p1n1


example : R2.proj₁ Pt_0n1 = ⟨ 0 ⟩ := 
begin
 rw R2.proj₁,
 rw [Pt_0n1],
end 


-- There are three functions ℝ³ → ℝ² made out of projections: 

def R3.proj_to_2d₁ (a : R3) : R2 := ⟨a.x, a.y⟩ 
def R3.proj_to_2d₂ (a : R3) : R2 := ⟨a.x, a.z⟩ 
def R3.proj_to_2d₃ (a : R3) : R2 := ⟨a.y, a.z⟩ 


lemma proj_comp₁ : R2.proj₁ ∘ R3.proj_to_2d₁ = R3.proj₁ := 
begin
  funext a, 
  simp, 
  rw [R3.proj_to_2d₁],
  rw [R2.proj₁],
  refl, --just prove x=x 
end 



-- Write down and prove six other lemmas corresponding to five different compositions. For instance:

lemma proj_comp₂ : R2.proj₂ ∘ R3.proj_to_2d₁ = R3.proj₂ := 
begin
  funext, 
  refl,
end 

lemma proj_comp₃ : R2.proj₁ ∘ R3.proj_to_2d₂ = R3.proj₁ := 
begin
  funext, 
  refl,
end 

lemma proj_comp₄ : R2.proj₂ ∘ R3.proj_to_2d₂ = R3.proj₃ := 
begin
  funext, 
  refl,
end 

lemma proj_comp₅ : R2.proj₁ ∘ R3.proj_to_2d₃ = R3.proj₂ := 
begin
  funext, 
  refl,
end 

lemma proj_comp₆ : R2.proj₂ ∘ R3.proj_to_2d₃ = R3.proj₃ := 
begin
  funext, 
  refl,
end 



/-!  #### Addition
Similar to the addition of real numbers, we can add affine points. You know this from the vector addition. 
-/

def R1.add (a b : R1) : R1 := ⟨a.x + b.x⟩ 

def R1_add_alt (a b : ℝ) : ℝ := a + b 

def R2.add (a b : R2) : R2 := ⟨a.x + b.x, a.y + b.y⟩

def R3.add (a b : R3) : R3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

#check R3.add

-- #eval R2.add Pt_0n1 Pt_0p1
-- #eval R3.add Pt_n1p1n1 Pt_p1n1p1


/- 
It is often convenient to use anonymous projection notation, which allows us to write `P₁ .add P₂` instead of `R2.add P₁ P₂`. 
-/

example :  Pt_0n1 .add Pt_0p1 = ⟨0, 0⟩ :=
begin
  ext,
  repeat 
  {
    unfold R2.add,
    rw [Pt_0n1, Pt_0p1], 
    ring_nf,
  },
end 


example :  Pt_n1p1n1 .add Pt_p1n1p1 = ⟨0, 0, 0⟩ :=
begin
  ext,
  repeat {
    unfold R3.add,
    rw [Pt_n1p1n1, Pt_p1n1p1], 
    ring_nf,
  },
end 


/- 
Below we name our theorem `R2.add_comm` to avoid ambiguity with a generic theorem like `add_comm`.
-/ 

theorem R2.add_comm (a b : R2) : 
   a .add b = b .add a :=
begin
  -- rw [R2.add, R2.add],
  unfold R2.add, 
  ext, 
  dsimp,
  repeat {apply add_comm},
end 


#check add_comm
#check R2.add_comm


--Challenge: Prove the theorem above for points in the 3-d space. 
theorem R3.add_comm (a b :R3) : a .add b =  b .add a :=
begin
  unfold R3.add, 
  ext,
  repeat { apply add_comm },
end


-- challenge: prove the associativity of addition in 2 and 3 dimensions

theorem R2.add_assoc (a b c : R2) : 
   (a .add b) .add c =  a .add (b .add c) :=
  begin
    unfold R2.add,
    ext,
    repeat {simp},
    repeat {apply add_assoc},
  end 

theorem R3.add_assoc (a b c : R3) : 
 (a .add b) .add c = a .add ( b .add c) :=
begin
  unfold R3.add, 
  ext,
  repeat {simp},
  repeat {apply add_assoc},
end 


--Challenge: We can prove the associativity of addition in 2d from as the associativity of addition in 3d where the last (z) coordinate is 0 for points a b c. Can you implement this idea in Lean?


/- 
Consider the following "embeddings" (draw a geometric picture of these maps)
-/


def R1.embed₁  (a : R1) : R2 := 
{ 
  x := a.x,
  y := 0,
}

def R1.embed₂  (a : R1) : R2 := 
{ 
  x := 0,
  y := a.x,
}

-- the three embeddings which keep x-axis fixed:
def R2.xembed₁  (a : R2) : R3 := 
{ 
  x := a.x,
  y := a.y,
  z := 0,
}

def R2.xembed₂  (a : R2) : R3 := 
{ 
  x := a.x,
  y := 0,
  z := a.y,
}

def R2.xembed₃  (a : R2) : R3 := 
{ 
  x := 0,
  y := a.x,
  z := a.y,
}





/-! ### Algebraic Structures-/


structure preorder_bundled:= 
(carrier : Type) -- a type of carrier (as underlying type)
(rel : carrier → carrier → Prop) -- a binary relation saying when two elements of the carrier are related to each to other
(rflx : reflexive rel) -- this is an axiom/propety of relation `rel` saying that any term/element is related to itself. 
(trns : transitive rel) -- this is an axiom/propety of relation `rel` saying that if we have three terms and the first two of which are related to each other through the relation `rel` and the last two of which are related to each other through the relation `rel`, then the first and the third are related to each other through the relation `rel` 


#check preorder_bundled.carrier -- the underlying type of preorder_bundled_bundledstructure
#check preorder_bundled.rflx
#check preorder_bundled.trns
#reduce preorder_bundled.trns 

#check transitive 
#reduce @transitive



#check preorder_bundled.carrier -- the underlying type of preorder_bundled structure
#check preorder_bundled.rflx



-- an instance of a preorder_bundled structure 
def preorder_bundled_nat_eq : preorder_bundled := 
{
  carrier := ℕ, 
  rel := λ m, λ n, m = n, 
  rflx := by {unfold reflexive,intro x, refl, },
  trns := by {unfold transitive, apply eq.trans,}, 
}



#check preorder_bundled_nat_eq
#print preorder_bundled_nat_eq

#reduce preorder_bundled.carrier preorder_bundled_nat_eq 
#reduce preorder_bundled_nat_eq.carrier 



#check preorder_bundled_nat_eq
#print preorder_bundled_nat_eq

#reduce preorder_bundled.carrier preorder_bundled_nat_eq 
#reduce preorder_bundled_nat_eq.carrier 


#reduce preorder_bundled_nat_eq.rflx 




def preorder_bundled_nat_le : preorder_bundled := 
{
  carrier := ℕ, 
  rel := λ m, λ n, m ≤ n, 
  rflx := by {unfold reflexive,intro x, refl, },
  trns := by {unfold transitive, apply le_trans,}, 
}


section
variables b b' : bool 
#check b && b'  
#eval ff && tt
#eval tt && tt 
end 



 
@[simp] 
def bool_and : bool → bool → bool 
| _  ff  := ff 
| ff _ := ff
| tt  tt := tt


lemma bool_and_assoc {x y z : bool}  : 
  x && y && z = x && (y && z) := 
begin
simp,  
end 

 


def preorder_bundled_bool : preorder_bundled := 
{
  carrier := bool, 
  rel := λ b, λ b', b && b' = b, 
  rflx := by { unfold reflexive, 
               intro x, --   
               cases x, 
               repeat {refl}, 
               },
  trns := by { unfold transitive, 
               intros x y z, 
               intros h₁ h₂, rw ← h₁, rw bool_and_assoc, rw h₂}, 
}



/- Morphisms between preorders -/
structure preorder_bundled.morphism := 
(dom cod : preorder_bundled)
(to_fun : dom.carrier → cod.carrier) 
(respect_rel : ∀ {a b : dom.carrier}, dom.rel a b → cod.rel (to_fun a) (to_fun b))


/- An instance of a morphism between two preorders on natural numbers-/
def preorder_bundled_nat_eq_to_nat_le : preorder_bundled.morphism := 
{
  dom := preorder_bundled_nat_eq, 
  cod := preorder_bundled_nat_le, 
  to_fun := id, 
  respect_rel := by {intros a b, simp, apply le_of_eq, }
}




end STR 


-- STR.


end PROOFS 

-- PROOFS.STR.