#check Empty

-- inductive Empty : Type

inductive Chaos : Type

def from_empty (e : Empty) : Chaos := nomatch e

#check False
--inductive False : Prop

def from_false (P : Prop) (p : False) : P := False.elim p
--.elim is prop equivalent of nomatch for empty

def from_false_true_is_false (p : False) : True = False := False.elim p

/-!
Unit ==> True
-/

#check Unit
--inductive Punit : Sort u where
-- | unit : Punit

#check True
-- inductive Type : Prop where
-- | intro : True

#check True.intro

def proof_of_true : True := True.intro

def false_implies_true : False → True := λ f => False.elim f

-- Prod ==> And

#check Prod

/-!
structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β
-/

#check And
/-!
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
-/

inductive Birds_chirping : Prop
| yep
| boo

inductive Sky_blue : Prop
| yep

#check (And Birds_chirping Sky_blue)

theorem both_and : And Birds_chirping Sky_blue := And.intro Birds_chirping.boo Sky_blue.yep

/-!
Proof Irrelevance
-/

namespace cs2120f23
inductive Bool : Type
| true
| false

theorem proof_equal : Birds_chirping.boo = Birds_chirping.yep := by trivial

-- in prop all proofs are equivalent, so doesnt influence computations

-- Sum ==> Or

#check Sum
/-!
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
-/

#check Or

/-!
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

theorem one_or_other : Or Birds_chirping Sky_blue := Or.inl Birds_chirping.yep
theorem one_or_other' : Or Birds_chirping Sky_blue := Or.inr Sky_blue.yep

example : Or Birds_chirping (0=1) := Or.inl Birds_chirping.yep
example : (0=1) ∨ (1=2) := _

theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P :=
λ d =>
  match d with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q

-- Not (no)

def no (α : Type) := α → Empty

#check Not
--Not P is defined to be P → False

example: no Chaos := λ (c : Chaos) => nomatch c

inductive Raining : Prop
example : ¬ Raining := λ (r : Raining) => nomatch r
