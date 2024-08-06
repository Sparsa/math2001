-- This is the chapter 5 of the book theorem proving using lean4.
-- by definition tactics are commands, or instructions that describe ho to build such a proof.
-- When you work on a mathematical proof, you say things like,
-- 1. to prove the forward direction
-- 2. unfold the definition
-- 3. apply the previous lemma
-- 4. or simply simplify
-- Just like these tactics are instructions that tell Lean how to construct a proof term.
-- the proofs will be a sequence of tactics and will be known as tactic style proof.
-- tactic style proofs are easy to write but harder to read
-- These kind of proofs are the gateway of leans automataion.
-- *have* keyword creates a goal
theorem test (p q : Prop) (hp: p) (hq: q) : p∧q ∧ p :=
by apply And.intro hp
   apply And.intro hq hp
#print test
-- you can also write multiple tactics in a single line usig semicolon as separator.
-- The apply tactic applies an expression, viewed as denoting a function with zero or more arguments
--
-- tactics that may produce multiple subgoals and often tag them
-- the tactic apply And.intro has two subgoals and it tagged them as Left
-- structured version
theorem test1 (p q : Prop) (hp: p) (hq :q) : p ∧ q ∧ p := by
        apply And.intro
        case right =>
             apply And.intro
             case left => exact hq
             case right => exact hp
        case left => exact hp

-- lean hides other goals inside the case block. We say it is focusing on the selected goal.
-- -- lean flags an error if the selected goal is not fully solved at the end of the case block.
-- other than already used apply and exact tactics, we also use the following tactics.
-- intro : which introduces a hypothesis
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q ) ∨ (p ∧ r) := by
        apply Iff.intro
        . intro h -- assume that the left is h
          apply Or.elim (And.right h) -- now apply or elimination in the right of the and
          . intro hq -- assume the q is true
            apply Or.inl -- introduce topmost or
            apply And.intro -- then you can introduce And
            . exact And.left h
            . exact hq
          . intro hr
            apply Or.inr
            apply And.intro
            . exact And.left h
            . exact hr
        . intro h
          apply Or.elim h
          . intro hpq
            apply And.intro
            . exact And.left hpq
            . apply Or.inl -- because to introduce or only one truth value is sufficient
              exact And.right hpq
          . intro hpr
            apply And.intro
            . exact And.left hpr
            . apply Or.inr
              exact And.right hpr

-- the tactic commands can take compound expressions, not just single identifiers
theorem test2 (p q : Prop) (hp :p) (hq : q) : p ∧ q ∧ p := by
        apply And.intro hp
        exact And.intro hq hp

example (α : Type) : ∀ x :α, x = x := by
        intro x
        exact Eq.refl x -- reflexive relation

example : ∀ a b c : Nat, a = b → a = c → c = b := by
        intro a b c h_1 h_2 -- this is naming the assumptions
        exact Eq.trans (Eq.symm h_2) h_1 -- it is applying symmetricity on a = c, which givs us c = a, then it is applying transitivity with b  = a
-- the above goal can be written as
-- p : Prop, q:Prop, hp:p, hq :q, q ⊢p∧q∧p :=
-- the apply tactic is a command for constructing function applications
-- interactively the intro tactic is a command for constructing function abstraction
-- terms of the form fun x => e.
-- as with lambda abstration notation, the intro tactic allows us to use an implicit match

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x , q x ∧ p x := by
       intro ⟨w, hpw, hqw⟩
       exact ⟨w, hqw, hpw⟩

-- You can also provide multiple alternatives like in the match expression
example (α : Type ) (p q : α → Prop) : (∃ x, p x ∨ q x ) → ∃ x, q x ∨ p x := by
intro
| ⟨ w, Or.inl h⟩ => exact ⟨ w, Or.inr h⟩
| ⟨ w, Or.inr h ⟩ => exact ⟨ w, Or.inl h⟩

-- The `intros` tactic c an be used without any arguments
-- In which case it chooses names and introduces as many variables as it can

-- the `assumption` can be used without any arguments,
-- in which case, it chooses names and introduces as man variables as it can.

example (x y z w : nat) (h₁ : x =y) (h₂ : y = z) (h₃ : z = w) := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption

-- it will unify metavariables in the conclusion if necessary
example (w y z w : nat) (h₁ : x  = y ) (h₂ : y = z ) (h₃ : z = w) : x = w := by
apply Eq.trans
assumption -- solves x = ?b with h₁
apply Eq.trans
assumption
assumption


-- the following example uses intros command to introduce the three variable and two hypothesis
-- automatically
example : ∀ a b c : nat , a = b → a = c→ c = b := by
intros -- this introdueses hab(a=b) and hac(a=c),
apply Eq.trans -- this uses hab and hac and applies transitivity to get (b= c)
apply Eq.symm -- this uses symmetry to get (c=b) from (b=c)
assumption
assumption
-- also why is it repeating assumtions twice?
-- I found that you can write `repeat assumption` instead of writing `assumption` twice
--- the question is why it is asking for assumptions?
-- What is `rfl` tactic?
-- it is a syntactic sugar of `exact rfl`
-- note that nat and Nat are two different types, do not confuse them else you will
-- get type mismatch
example (y : Nat) : (fun x: Nat => 0) y = 0 := by
rfl -- ok this meas `reflexive`
-- tactic `revrt`, it is inverse of `intro`
example (x : Nat) : x = x := by
revert x
intro y
rfl
-- moving an hypothesis into the goal yields an implication

example (x y : Nat) (h:x=y) : y = x:= by
  revert h -- what do you mean by this? as pointed out previoulsy
  -- this means that you are moving an hypothesis in the goal, making it an implication
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁ -- goal is x y :Nat , h₁ : x = y ⊢ y = x
  -- Intro makes a precondition to a hypothesys
  -- revert makes a hypothesys a precondition
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y ) :y = x := by
apply Eq.symm h
 -- clearly the `intro` and `revert` are inverse of each other

-- `revert` only works on an element of the local context
-- you can replace an artibrary expression in th goal by a fresh variable using
-- `generalize` tactic
example : 3 = 3 := by
generalize 3 = x
-- you are uplifting 3 to an abstract interpretation of `x`
-- if you can prove that for all x : Nat x = x then you are done
revert x -- add it back to the goal
intro y -- use the same steps we have done before
rfl
-- note that just like any other abstraction techniques this `generalize` tactic
-- have to be implemented very carefully becasue not all application will preserve the validiity
-- of the goal
-- one such simple example is
example : 2 + 3 = 5 := by
generalize 3 = x
admit
 -- adit tactic is analgue of the sorry it closes the current goal, producing the usual warning that hte sorry has been used.


 - 
