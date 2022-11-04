/- 
Structures with Type Classes
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

/-! ## Type Classes 

A __type class__ is a structure type combining abstract constants and their
properties. A type can be declared an instance of a type class by providing
concrete definitions for the constants and proving that the properties hold.
Based on the type, Lean retrieves the relevant instance. -/

#print inhabited

#check nat.inhabited

@[instance] def nat_inhabited : inhabited ℕ :=
{ default := 0 }

@[instance] def list.inhabited {α : Type} :
  inhabited (list α) :=
{ default := [] }

#eval inhabited.default ℕ          -- result: 0
#eval inhabited.default (list ℤ)   -- result: []

def head {α : Type} [inhabited α] : list α → α
| []       := inhabited.default α
| (x :: _) := x

lemma head_head {α : Type} [inhabited α] (xs : list α) :
  head [head xs] = head xs :=
begin
  cases' xs,
  { refl },
  { refl }
end

#eval head ([] : list ℕ)   -- result: 0

#check list.head

@[instance] def fun.inhabited {α β : Type} [inhabited β] :
  inhabited (α → β) :=
{ default := λa : α, inhabited.default β }

inductive empty : Type

@[instance] def fun_empty.inhabited {β : Type} :
  inhabited (empty → β) :=
{ default := λa : empty, match a with end }

@[instance] def prod.inhabited {α β : Type}
    [inhabited α] [inhabited β] :
  inhabited (α × β) :=
{ default := (inhabited.default α, inhabited.default β) }

/-! Here are other type classes without properties: -/

#check has_zero
#check has_neg
#check has_add
#check has_one
#check has_inv
#check has_mul

#check (1 : ℕ)
#check (1 : ℤ)
#check (1 : ℝ)

/-! We encountered these type classes in lecture 2: -/

#print is_commutative
#print is_associative


/-! ## Lists
`list` is an inductive polymorphic type constructed from `nil` and `cons`: -/

#print list

/-! `cases'` can also be used on a hypothesis of the form `l = r`. It matches `r`
against `l` and replaces all occurrences of the variables occurring in `r` with
the corresponding terms in `l` everywhere in the goal. -/

lemma injection_example {α : Type} (x y : α) (xs ys : list α)
    (h : list.cons x xs = list.cons y ys) :
  x = y ∧ xs = ys :=
begin
  cases' h,
  cc
end

/-! If `r` fails to match `l`, no subgoals emerge; the proof is complete. -/

lemma distinctness_example {α : Type} (y : α) (ys : list α)
    (h : [] = y :: ys) :
  false :=
by cases' h

def map {α β : Type} (f : α → β) : list α → list β
| []        := []
| (x :: xs) := f x :: map xs

def map₂ {α β : Type} : (α → β) → list α → list β
| _ []        := []
| f (x :: xs) := f x :: map₂ f xs

#check list.map

lemma map_ident {α : Type} (xs : list α) :
  map (λx, x) xs = xs :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end

lemma map_comp {α β γ : Type} (f : α → β) (g : β → γ)
    (xs : list α) :
  map g (map f xs) = map (λx, g (f x)) xs :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end

lemma map_append {α β : Type} (f : α → β) (xs ys : list α) :
  map f (xs ++ ys) = map f xs ++ map f ys :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end

def tail {α : Type} : list α → list α
| []        := []
| (_ :: xs) := xs

#check list.tail

def head_opt {α : Type} : list α → option α
| []       := option.none
| (x :: _) := option.some x

def head_pre {α : Type} : ∀xs : list α, xs ≠ [] → α
| []       hxs := by cc
| (x :: _) _   := x

#eval head_opt [3, 1, 4]
#eval head_pre [3, 1, 4] (by simp)
-- fails
#eval head_pre ([] : list ℕ) sorry

def zip {α β : Type} : list α → list β → list (α × β)
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys
| []        _         := []
| (_ :: _)  []        := []

#check list.zip

def length {α : Type} : list α → ℕ
| []        := 0
| (x :: xs) := length xs + 1

#check list.length

/-! `cases'` can also be used to perform a case distinction on a proposition, in
conjunction with `classical.em`. Two cases emerge: one in which the proposition
is true and one in which it is false. -/

#check classical.em

lemma min_add_add (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
begin
  cases' classical.em (m ≤ n),
  case inl {
    simp [min, h] },
  case inr {
    simp [min, h] }
end

lemma min_add_add₂ (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
match classical.em (m ≤ n) with
| or.inl h := by simp [min, h]
| or.inr h := by simp [min, h]
end

lemma min_add_add₃ (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
if h : m ≤ n then
  by simp [min, h]
else
  by simp [min, h]

lemma length_zip {α β : Type} (xs : list α) (ys : list β) :
  length (zip xs ys) = min (length xs) (length ys) :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : x xs' {
    cases' ys,
    case nil {
      refl },
    case cons : y ys' {
      simp [zip, length, ih ys', min_add_add] } }
end

lemma map_zip {α α' β β' : Type} (f : α → α') (g : β → β') :
  ∀xs ys,
    map (λab : α × β, (f (prod.fst ab), g (prod.snd ab)))
      (zip xs ys) =
    zip (map f xs) (map g ys)
| (x :: xs) (y :: ys) := by simp [zip, map, map_zip xs ys]
| []        _         := by refl
| (_ :: _)  []        := by refl


/-! ## Binary Trees
Inductive types with constructors taking several recursive arguments define
tree-like objects. __Binary trees__ have nodes with at most two children. -/

inductive btree (α : Type) : Type
| empty {} : btree
| node     : α → btree → btree → btree

/-! The type `aexp` of arithmetic expressions was also an example of a tree data
structure.
The nodes of a tree, whether inner nodes or leaf nodes, often carry labels or
other annotations.
Inductive trees contain no infinite branches, not even cycles. This is less
expressive than pointer- or reference-based data structures (in imperative
languages) but easier to reason about.
Recursive definitions (and proofs by induction) work roughly as for lists, but
we may need to recurse (or invoke the induction hypothesis) on several child
nodes. -/

def mirror {α : Type} : btree α → btree α
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node a (mirror r) (mirror l)

lemma mirror_mirror {α : Type} (t : btree α) :
  mirror (mirror t) = t :=
begin
  induction' t,
  case empty {
    refl },
  case node : a l r ih_l ih_r {
    simp [mirror, ih_l, ih_r] }
end

lemma mirror_mirror₂ {α : Type} :
  ∀t : btree α, mirror (mirror t) = t
| btree.empty        := by refl
| (btree.node a l r) :=
  calc  mirror (mirror (btree.node a l r))
      = mirror (btree.node a (mirror r) (mirror l)) :
    by refl
  ... = btree.node a (mirror (mirror l)) (mirror (mirror r)) :
    by refl
  ... = btree.node a l (mirror (mirror r)) :
    by rw mirror_mirror₂ l
  ... = btree.node a l r :
    by rw mirror_mirror₂ r

lemma mirror_eq_empty_iff {α : Type} :
  ∀t : btree α, mirror t = btree.empty ↔ t = btree.empty
| btree.empty        := by refl
| (btree.node _ _ _) := by simp [mirror]

