/-
An excerpt from the Theory of Deduction section in the Principia:

“The purpose of the present section is to set forth the first stage of the
deduction of pure mathematics from its logical foundations. This first stage is
necessarily concerned with deduction itself, i.e., with the principles by which
conclusions are inferred from premises.”

-/

/-

I used the word "ast" to replace "*" and underscore "_" to replace
"·" in the Principia. For example, Theorem "*2·08" becomes "ast_2_08".

Any comment related to a specific theorem should precede the theorem and never
follow it. Quoted comments are those made in the Principia concerning a
particular theorem or definition.

Except for a very few usages of Mathlib's builtin logic theorems, this work is
expected to be self-contained­meaning that almost all of the theorems are
derived using previous ones.

-/

import Mathlib.Logic.Basic


namespace Principia.Part1.Section1

-- PRIMITIVE IDEAS

--- ∗1.01: p ⊃ q .=. ~ p ∨ q Df. (Here the letters "Df" stands for definition)
theorem ast_1_01 (p q: Prop) : (p → q) = (¬p ∨ q) := by
  apply propext
  exact imp_iff_not_or

-- PRIMITIVE PROPOSITIONS

--- ∗1.1: Anything implied by a true elementary proposition is true.
theorem ast_1_1 (p q: Prop) : (p → q) → (p → q) /- Modus Ponens -/ := by
  intro p q
  exact p q

--- *1.2 ⊢: p ∨ q . ⊃ . p (tautology)
theorem ast_1_2 (p: Prop) : (p ∨ p) → p := by
  intro _
  simp_all only [or_self]

--- *1.3 ⊢: p ∨ q . ⊃ . q ∨ p

--- “This principle states: ‘If q is true, then ‘p or q’ is true.’ Thus e.g., if
--- q is ‘to-day is Wednesday’ and p is ‘to-day is Tuesday,’ the principle
--- states: ‘If to-day is Wednesday, then to-day is either Tuesday or
--- Wednesday.’ It is called the ‘principle of addition,’ because it states that
--- if a proposition is true, any alternative may be added without making it
--- false. the principle will be referred to as ‘Add.”

theorem ast_1_3 (p q: Prop) : q → (p ∨ q) := by
  intro a
  exact Or.inr a

--- *1.4 ⊢: p ∨ q . ⊃ . q ∨ p

--- “This principles states that ‘p or q’ implies ‘q or p.’ It states the
--- permutative law for logical addition of proposition, and will be called the
--- ‘principle of permutation’ because it states that if a proposition is true,
--- any alternative may be added without making it false. The principle will be
--- referred to as ‘Perm.’
theorem ast_1_4 (p q: Prop) : (p ∨ q → q ∨ p) := by
  intro a
  exact Or.symm a

--- *1.5 ⊢: p ∨ (q ∨ r) . ⊃ . ∨ (p ∨ r)

--- “This principle states: ‘If either p is true, or ‘q or r’ is true, then
--- either q is true, or ‘p or r’ is true.’ It is a form of the associative law
--- for logical addition, and will be called ‘associative principle.’ It will be
--- referred to as ‘Assoc.’ The proposition p ∨ (q ∨ r) . ⊃ . (p ∨ q) ∨ r, which
--- would be the natural form for the associative law, has less deductive power,
--- and is therefore not taken as the primitive proposition.

theorem ast_1_5 (p q r: Prop) : p ∨ (q ∨ r) → q ∨ (p ∨ r) := by
  intro a
  exact or_left_comm.mp a

--- *1.6 ⊢ :. q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r

--- “This principle states: ‘If q implies r, then ‘p or q’ implies ‘p or r.’’ In
--- other words, in an implication, an alternative may be added to both
--- premisses and conclusion without impairing the truth of the implication. The
--- principle will be called the ‘principle of summation,’ and will be referred
--- to as ‘Sum.’”

theorem ast_1_6 (p q r: Prop) : (q → r) → (p ∨ q → p ∨ r) := by
  intro a
  exact λ b ↦ Or.imp_right a b

-- *2 IMMEDIATE CONSEQUENCES OF THE PRIMITIVE PROPOSITIONS

--- *2.01 ⊢: p ⊃ ~p . ⊃ . ~p

--- This proposition states that, if p implies its own falsehood, then p is
--- false. It is called the ‘principle of the reductio ad absurdum’ and will be
--- referred to as ‘Abs.’ The proof is as follows (where ‘Dem.’ is short for
--- ‘demonstration’):
theorem ast_2_01 (p: Prop) : (p → ¬p) → ¬p := by
  -- Dem.
  /-
  $\left[ \text{Taut}\frac{\sim p}{p}\right] \vdash: \sim p \vee \sim p . \supset . \sim p$
  -/
  have Taut := ast_1_2
  specialize Taut ¬p
  /- [(1).(*1.01)] \vdash : p \supset ~p . \supset . ~p -/
  rw [<- ast_1_01] at Taut
  exact Taut


theorem ast_2_02 (p q: Prop) : q → (p → q) := by
  have Add := ast_1_3
  -- Dem.
  /-
  $\left[ \text{Add}\frac{\sim p}{p}\right] \vdash: q . \supset . \sim p \vee q$
  -/

  specialize Add (¬p) q
  /- $[(1).(*1.01)] \vdash : p \supset \sim p . \supset . \sim p$-/
  rw [<- ast_1_01 p q] at Add
  exact Add


theorem ast_2_03 (p q: Prop) : (p → ¬q) → (q → ¬p) := by
  -- Dem.
  /-
  $\left[ \text{Perm}\frac{\sim p,\ \sim q}{p,\ q}\right] \vdash: \sim p \vee \sim q . \supset . \sim q \vee \sim p$
  -/

  have Perm := ast_1_4
  specialize Perm (¬p) (¬q)
  /- $[(1).(*1.01)] \vdash : p \supset \sim q . \supset . q \supset \sim p$ -/
  repeat rw [<- ast_1_01] at Perm
  exact Perm


-- “This is called the ‘commutative principle’ and referred to as ‘Comm.’ It
-- states that, if r follows q provided p is true, then r follows from p
-- provided q is true.”
theorem ast_2_04 (p q r: Prop) : (p → (q → r)) → (q → (p → r)) := by
  -- Dem.
  /-
  $\left[ \text{Assoc}\frac{\sim p,\ \sim q}{p,\ q}\right] \vdash:. \sim p \vee (\sim q \vee r) . \supset . \sim q \vee (\sim p \vee r)$
  -/

  have Assoc := ast_1_5
  specialize Assoc (¬p) (¬q) r
  /- $[(1).(*1.01)] \vdash :. p . \supset . q \supset r : \supset : q . \supset . p \supset r$ -/
  repeat rw [<- ast_1_01] at Assoc
  exact Assoc

-- “These two propositions [ast_2_05 & ast_2_06] are the source of the syllogism
-- in Barbara (as will be shown later) and are therefore called the ‘principle
-- of syllogism’ (referred to as ‘Syll’). The first states that, if r follows
-- from q, then if q follows from p, r follows from p. The second states the
-- same thing with the premisses interchanged”
theorem ast_2_05 (p q r: Prop) : (q → r) → ((p → q) → (p → r)) := by
  -- Dem.
  /-
  $\left[ \text{Sum}\frac{\sim p}{p}\right] \vdash:. q \supset r . \supset : \sim p \vee q . \supset . \sim p \vee r$
  -/
  have Sum := ast_1_6
  specialize Sum (¬p) q r
  /- $[(1).(*1.01)] \vdash :. q \supset r . \supset : p \supset q . \supset . p \supset r$ -/
  repeat rw [<- ast_1_01] at Sum
  exact Sum

theorem ast_2_06 (p q r: Prop) : (p → q) → ((q → r) → (p → r)) := by
  -- Dem.
  /-
  $\left[ \text{Comm}\frac{q \supset r,\ p \supset q,\ p \supset r}{p,\ q,\ r}\right] \vdash :: q \supset r . \supset : p \supset q. \supset . p \supset r :. \supset :. p \supset q . \supset : q \supset r . \supset . p \supset r$
  -/
  have Comm := ast_2_04 (q → r) (p → q) (p → r)
  /-
  $[*2\cdot 05] ⊢:. q \supset r . \supset : p \supset q . \supset . p \supset r$
  -/
  have Syll := ast_2_05
  -- TODO: Prof. Russell uses Syll q r p instead and applies *1.11
  specialize Syll p q r
  exact Comm <| Syll

-- “Here we put nothing beyond ‘*1.3 p/q,’ because the proposition to be proved
-- is what *1.3 becomes when p is written in place of q.
theorem ast_2_07 (p: Prop) : p → (p ∨ p) := ast_1_3 /- Add -/ p p

theorem ast_2_08 (p: Prop) : p → p := by
  -- Dim
  /-
  $\left[ \ast\text{2.05}\ \frac{p \vee p,\ p}{q,\ \ r} \right] \vdash ::  p \vee p . \supset . p : \supset :. p . \supset . p \vee p : \supset . p \supset p$
  -/

  have Syll := ast_2_05 p (p ∨ p) p
  /-
  $\left[ \text{Taut} \right] \vdash: p \vee p . \supset . p$
  -/
  have Taut := ast_1_2 p
  /- $[\ast 2.07] \vdash : p . \supset . p \vee p$ -/
  have ast_2_07 := ast_2_07 p
  exact (Syll <| Taut) <| ast_2_07

theorem ast_2_1 (p : Prop) : (¬p) ∨ p := by
  have ast_2_08 := ast_2_08 p
  rw [ast_1_01] at *
  exact ast_2_08

-- “This is the law of excluded middle.”
theorem ast_2_11 (p : Prop) : p ∨ (¬p) := by
  -- Dim
  /-
  $\left[ \text{Perm}\frac{\sim p,\ p}{p,\ q}\right] \vdash: \sim p \vee p . \supset . p \vee \sim p$
  -/
  have Perm := ast_1_4
  specialize Perm (¬p) p
  have ast_2_1 := ast_2_1 p
  exact Perm <| ast_2_1

theorem ast_2_12 (p :  Prop) : p → ¬(¬p) := by
  have ast_2_11 := ast_2_11
  specialize ast_2_11 (¬p)
  rw [<- ast_1_01] at ast_2_11
  exact ast_2_11

-- “This proposition is a lemma for *2.14, which, with *2.12 constitutes the
-- principle of double negation”
theorem ast_2_13 (p: Prop) : p ∨ (¬(¬(¬p))) := by
  have Sum := ast_1_6
  specialize Sum p (¬p) (¬(¬(¬p)))
  have ast_2_12 := ast_2_12
  specialize ast_2_12 ¬p
  have ast_2_11 := ast_2_11
  specialize ast_2_11 p
  exact (Sum <| ast_2_12) <| ast_2_11


theorem ast_2_14 (p : Prop) : (¬(¬p)) → p := by
  have Perm := ast_1_4
  specialize Perm p (¬(¬(¬p)))
  have ast_2_13 := ast_2_13
  specialize ast_2_13 p
  rw [<- ast_1_01] at Perm
  exact Perm <| ast_2_13

theorem ast_2_15 (p q: Prop) : (¬p → q) → (¬q → p) := by
  have ast_2_05 := ast_2_05
  have ast_2_12 := ast_2_12
  have ast_2_03 := ast_2_03
  have ast_2_05' := ast_2_05
  have ast_2_05'' := ast_2_05
  have ast_2_05''' := ast_2_05
  -- To reuse the theorem, I had to change the order I usually follow of `have`
  -- and `specialize`
  specialize ast_2_12 q
  specialize ast_2_05 (¬p) q (¬(¬q))

  have ast_2_14 := ast_2_14
  specialize ast_2_14 p
  specialize ast_2_05'' (¬p → q) (¬p → (¬(¬q))) (¬q → (¬(¬p)))

  -- [(1).(2).*1.11]
  have _3 := ast_2_05 <| ast_2_12 -- (3)
  specialize ast_2_03 (¬p) (¬q) -- (4)
  specialize ast_2_05' (¬q) (¬(¬p)) p -- (5)
  -- [(5).*2.14.*1.11]
  have _6 := ast_2_05' <| ast_2_14
  -- [(4).(7).*1.11]
  have _8 := ast_2_05'' <|  ast_2_03

  have _9 := _8 <| _3
  -- (10)
  specialize ast_2_05''' (¬p → q) (¬q → (¬(¬p))) (¬q → p)
  have _11 := ast_2_05''' <| _6
  exact _11 <| _9

-- “Note on the proof of *2.15. In the above proof, it will be see that
-- (3), (4), (6) are respectively of the forms p₁ ⊃ p₂, p₂ ⊃ p₃, p₃ ⊃ p₄, where
-- p₁ ⊃ p₄ is the proposition to be proved. From p₁ ⊃ p₂, p₂ ⊃ p₃, p₃ ⊃ p₄ the
-- proposition p₁ ⊃ p₄ results by repeated applications of *2·05 or *2·06 (both
-- of which are called ‘Syll’). It is tedious and unnecessary to reaeat this
-- process every time it is used; it will therefore be abbreviate into
-- ‘[Syll] ⊢ -- .(a).(b).(c).⊃ ⊢ . (d),’

open Lean Meta Elab Tactic Term

structure ImpProof where
  (ant cons : Expr)
  (proof : Expr)
  deriving Inhabited

theorem compose {p q r : Prop} (a : p → q) (b : q → r) : p → r :=
  b ∘ a

/-- Compose two implication proofs using the `compose` theorem. -/
def ImpProof.compose (a : ImpProof) (b : ImpProof) : MetaM ImpProof := do
  unless ← isDefEq a.cons b.ant do
    throwError "\
      Consequent{indentD a.cons}\n\
      is not definitionally equal to antecedent{indentD b.ant}"
  let proof := mkApp5 (.const ``compose []) a.ant a.cons b.cons a.proof b.proof
  return { ant := a.ant, cons := b.cons, proof := proof }

/-- Create the proof of `p -> p` using the `id` function. -/
def ImpProof.rfl (p : Expr) : ImpProof :=
  { ant := p, cons := p, proof := .app (.const ``id [.zero]) p}

syntax "Syll" (ppSpace "[" term,* "]")? : tactic

-- TODO: a pedantic change would be to process the hypotheses in reverse order.
elab_rules : tactic
  | `(tactic| Syll $[[$[$terms?],*]]?) => withMainContext do

    -- Elaborate all the supplied hypotheses, or use the entire local context if not provided.
    let hyps ←
      match terms? with
      | none => getLocalHyps
      | some terms => terms.mapM fun term => Tactic.elabTerm term none

    liftMetaTactic1 fun goal => do
      let goalType ← goal.getType

      -- A list of implications extracted from `hyps`.
      let mut chain : Array ImpProof := #[]

      let getImplication? (e : Expr) : MetaM (Option (Expr × Expr)) := do
        -- There may be metadata and metavariables, so do some unfolding if
        -- necessary:
        let ty ← instantiateMVars (← whnfR e)
        -- Check if it is a non-dependent forall:
        if ty.isArrow then
          return (ty.bindingDomain!, ty.bindingBody!)
        else
          return none

      for hyp in hyps do
        match ← getImplication? (← inferType hyp) with
        | some (p, q) => chain := chain.push {ant := p, cons := q, proof := hyp}
        | none => logInfo m!"Expression {hyp} is not of the form `p → q`"

      let some (p, q) ← getImplication? goalType
        | throwError "Goal type is not of the form `p → q`"

      if chain.isEmpty then
        throwError "Local context has no implications"

      unless ← isExprDefEq chain[0]!.ant p do throwError "The first hypothesis
        does not match the goal's antecedent"

      unless ← isExprDefEq chain[chain.size - 1]!.cons q do throwError "The last
        hypothesis does not match the goal's consequent"

      let comp ← chain.foldlM (init := ImpProof.rfl p) (fun pf1 pf2 =>
      pf1.compose pf2)

      -- It's good to do one last check that the proof has the correct type
      -- before assignment.
      unless ← isDefEq (← inferType comp.proof) goalType do
        throwError "Invalid proof of goal"
      goal.assign comp.proof

      return none

-- where (a) is of the form p₁ ⊃ p₂, (b) of the form p₂
-- ⊃ p₃, (c) of the form p₃ ⊃ p₄, and (d) of the form p₁ ⊃ p₄. The same
-- abbreviation will be applied to a sorites of any length.”

theorem ast_2_16 (p q: Prop) : (p → q) → (¬q → ¬p) := by
  have ast_2_12 := ast_2_12
  specialize ast_2_12 q
  have ast_2_05 := ast_2_05
  specialize ast_2_05 p q (¬(¬q)) ast_2_12

  have ast_2_03 := ast_2_03
  specialize ast_2_03 p (¬q)
  Syll [ast_2_05, ast_2_03]

-- “Note. The proposition to be proved will be called ‘Prop,’ and when a proof
-- ends, like that of ∗2⬝16, by an implication between asserted propositions, of
-- which the consequence is the proposition to be proved, we shall write ‘⊢ .
-- etc. ⊃ ⊢ . Prop’. Thus ‘⊃ ⊢ . Prop’ ends a proof, and more or less
-- corresponds to ‘Q.E.D.’”

theorem ast_2_17 (p q: Prop) : (¬q → ¬p) → (p → q) := by
  have ast_2_03 := ast_2_03
  specialize ast_2_03 (¬q) p
  have ast_2_14 := ast_2_14
  specialize ast_2_14 q
  have ast_2_05 := ast_2_05
  specialize ast_2_05 p (¬(¬q)) q ast_2_14
  Syll [ast_2_03, ast_2_05]

-- ∗2⬝15, ∗2⬝16 and ∗2⬝17 are forms of the principle of transposition, and will
-- be all referred to as “Transp.”

theorem ast_2_18 (p: Prop) : (¬p → p) → p := by
  have ast_2_12 := ast_2_12
  specialize ast_2_12 p

  have ast_2_05 := ast_2_05
  specialize ast_2_05 (¬p) p (¬(¬p)) ast_2_12

  have ast_2_01 := ast_2_01
  specialize ast_2_01 (¬p)
  -- I deviated a little bit from how the proof was implemented in this step
  -- only because Syll finishes the goal rather than produces a hypotheses,
  -- TODO: perhaps I should change that.
  have ast_2_14 := ast_2_14
  specialize ast_2_14 p

  Syll [ast_2_05, ast_2_01, ast_2_14]

-- “This is the complement of the principle of the reductio ad absurdum. It
-- states that a proposition which follows from the hypothesis of its own
-- falsehood is true.”

theorem ast_2_2 (p q: Prop) : p → (p ∨ q) := by
  have Add := ast_1_3 q p
  have Perm := ast_1_4 q p
  Syll [Add, Perm]

theorem ast_2_21 (p q: Prop) : ¬p → (p → q) := by
  have ast_2_2 := ast_2_2 (¬p) q
  rw [<- ast_1_01] at ast_2_2
  exact ast_2_2

-- “The above two propositions are very frequently used.”

theorem ast_2_24 (p q: Prop) : p → (¬p → q) := by
  have ast_2_21 := ast_2_21 p q
  have Comm := ast_2_04 (¬p) p q
  exact Comm <| ast_2_21

theorem ast_2_25 (p q: Prop) : p ∨ ((p ∨ q) → q) := by
  have ast_2_1 := ast_2_1 (p ∨ q)
  have Assoc := ast_1_5  (¬(p ∨ q)) p q
  rw [ast_1_01]
  exact Assoc <| ast_2_1

theorem ast_2_26 (p q: Prop) : ¬p ∨ ((p → q) → q) := by
  have ast_2_25 := ast_2_25 (¬p) q
  rw [<- ast_1_01]
  repeat rw [<- ast_1_01] at ast_2_25
  exact ast_2_25

theorem ast_2_27 (p q: Prop) : p → ((p → q) → q) := by
  have ast_2_26 := ast_2_26 p q
  rw [<- ast_1_01] at ast_2_26
  exact ast_2_26

theorem ast_2_3 (p q r: Prop) : (p ∨ (q ∨ r)) → p ∨ (r ∨ q) := by
  have Perm := ast_1_4 q r
  have Sum := ast_1_6 p (q ∨ r) (r ∨ q)
  exact Sum <| Perm

-- “This proposition and ∗2·2 together constitute the associative law for for
-- logical addition of propositions. In the proof, the following abbreviation
-- (constantly used hereafter) will be employed∗: When we have a series of
-- propositions of the form a ⊃ b, b ⊃ c, c ⊃ d, all asserted, and ‘a ⊃ d’ is
-- the proposition to be proved, the proof in full is as follows: ”

theorem ast_2_31 (p q r: Prop) : p ∨ (q ∨ r) → (p ∨ q) ∨ r := by
  have ast_2_3 := (ast_2_3 p q r)
  have Assoc := ast_1_5 p r q
  have Perm := ast_1_4 r (p ∨ q)
  Syll [ast_2_3, Assoc, Perm]

theorem ast_2_32 (p q r: Prop) : (p ∨ q) ∨ r → p ∨ (q ∨ r) := by
  have Perm := ast_1_4 (p ∨ q) r
  have Assoc := ast_1_5 r p q
  have ast_2_3 := ast_2_3 p r q
  Syll [Perm, Assoc, ast_2_3]

-- This definition serves only for the avoidance of brackets.
def ast_2_33 (p q r: Prop) : (p ∨ q ∨ r) = ((p ∨ q) ∨ r) := by
  apply propext
  apply Iff.intro
  · exact ast_2_31 p q r
  · exact ast_2_32 p q r

theorem ast_2_36 (p q r: Prop) : (q → r) → ((p ∨ q) → (r ∨ p)) := by
  have Perm := ast_1_4 p r
  have ast_2_05 := ast_2_05 (p ∨ q) (p ∨ r) (r ∨ p) Perm
  have Sum := ast_1_6 p q r
  Syll [Sum, ast_2_05]

theorem ast_2_37 (p q r: Prop) : (q → r) → ((q ∨ p) → (p ∨ r)) := by
  intro qr
  have Perm := ast_1_4 q p
  have Sum := ast_1_6 p q r qr
  Syll [Perm, Sum]

theorem ast_2_38 (p q r: Prop) : (q → r) → ((q ∨ p) → (r ∨ p)) := by
  intro qr
  have Perm := ast_1_4 q p
  have Perm' := ast_1_4 p r
  have Sum := ast_1_6 p q r qr
  Syll [Perm, Sum, Perm']


-- “The proofs of ∗2·37·38 are exactly analogous to that of ∗2·36. (We use
-- ‘∗2·37·8’ as an abbreviation for ‘∗2·37 and ∗2·38.’ Such abbreviations will
-- be used throughout.)

theorem ast_2_4 (p q: Prop) : (p ∨ (p ∨ q)) → p ∨ q := by
  intro pq
  have ast_2_31 := ast_2_31 p p q
  have Taut := ast_1_2 p
  have ast_2_38 := ast_2_38 q (p ∨ p) p
  exact (ast_2_38 <| Taut) <| (ast_2_31 pq)

theorem ast_2_41 (p q: Prop) : (q ∨ (p ∨ q)) → p ∨ q := by
  intro qp
  have Assoc := ast_1_5 q p q
  have Taut := ast_1_2 q
  have Sum := ast_1_6 p (q ∨ q) q
  exact (Sum <| Taut) <| (Assoc qp)

theorem ast_2_42 (p q: Prop) : (¬p ∨ (p → q)) → (p → q) := by
  have ast_2_4 := ast_2_4 (¬p) q
  repeat rw [<- ast_1_01] at *
  exact ast_2_4

theorem ast_2_43 (p q: Prop) : (p → (p → q)) → (p → q) := by
  have ast_2_42 := ast_2_42 p q
  repeat rw [<- ast_1_01] at *
  exact ast_2_42

theorem ast_2_45 (p q: Prop) : ¬(p ∨ q) → ¬p := by
  have ast_2_2 := ast_2_2 p q
  have Transp := ast_2_16 p (p ∨ q)
  exact Transp <| ast_2_2

theorem ast_2_46 (p q: Prop) : ¬(p ∨ q) → ¬q := by
  have ast_1_3 := ast_1_3 p q
  have Transp := ast_2_16 q (p ∨ q)
  exact Transp <| ast_1_3

theorem ast_2_47 (p q: Prop) : ¬(p ∨ q) → ¬p ∨ q := by
  have ast_2_45 := ast_2_45 p q
  have ast_2_2 := ast_2_2 (¬p) q
  Syll [ast_2_45, ast_2_2]

theorem ast_2_48 (p q: Prop) : ¬(p ∨ q) → p ∨ ¬q := by
  have ast_2_46 := ast_2_46 p q
  have ast_1_3 := ast_1_3 p (¬q)
  Syll [ast_2_46, ast_1_3]

theorem ast_2_49 (p q: Prop) : ¬(p ∨ q) → ¬p ∨ ¬q := by
  have ast_2_45 := ast_2_45 p q
  have ast_2_2 := ast_2_2 (¬p) (¬q)
  Syll [ast_2_45, ast_2_2]

theorem ast_2_5 (p q: Prop) : ¬(p → q) → ¬p → q := by
  have ast_2_47 := ast_2_47 (¬p) q
  repeat rw [ast_1_01] at *
  exact ast_2_47

theorem ast_2_51 (p q: Prop) : ¬(p → q) → (p → ¬q) := by
  have ast_2_48 := ast_2_48 (¬p) q
  repeat rw [ast_1_01] at *
  exact ast_2_48

theorem ast_2_52 (p q: Prop) : ¬(p → q) → (¬p → ¬q) := by
  have ast_2_49 := ast_2_49 (¬p) q
  repeat rw [ast_1_01] at *
  exact ast_2_49

theorem ast_2_521 (p q: Prop) : ¬(p → q) → (q → p) := by
  intro pq
  exact ast_2_17 q p (ast_2_52 p q pq)

theorem ast_2_53 (p q: Prop) : (p ∨ q) → (¬p → q) := by
  intro pq
  rw [ast_1_01] at *
  exact (ast_2_38 q p ¬¬p <| ast_2_12 p) pq

theorem ast_2_54 (p q: Prop) : (¬p → q) → (p ∨ q) := by
  intro pq
  rw [ast_1_01] at *
  exact (ast_2_38 q (¬¬p) p <| ast_2_14 p) pq

theorem ast_2_55 (p q: Prop) : ¬ p → (p ∨ q) → q := by
  intro not_p
  have Comm := ast_2_04 (p ∨ q) (¬p) q
  exact (Comm <| ast_2_53 p q) not_p

theorem ast_2_56 (p q: Prop) : ¬q → (p ∨ q) → p := by
  intro not_q
  intro pq
  have Perm := ast_1_4 p q pq
  have ast_2_55 := ast_2_55 q p not_q
  exact ast_2_55 <| Perm
