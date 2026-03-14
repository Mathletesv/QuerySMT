import QuerySMT
import Aesop
import Mathlib.Tactic.Linarith

set_option auto.smt true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints true

set_option auto.smt.save false
set_option auto.smt.savepath "/Users/sreeram/Desktop/temp.smt"

set_option trace.duper.ignoredUnusableFacts true

set_option linter.deprecated true

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.proof true
set_option trace.auto.smt.parseTermErrors true

set_option trace.querySMT.debug true
set_option duper.throwPortfolioErrors false

set_option duper.collectDatatypes true
set_option auto.getHints.failOnParseError true

-- set_option querySMT.filterRedundancies false

-- set_option querySMT.filterHints false

-- set_option pp.universes true in
set_option pp.explicit true in
#check -Int.ofNat 1 * 5
-- this one shouldn't be bad

inductive myType2 (t : Type)
| const3 : t → myType2 t
| const4 : t → myType2 t

open myType2

example (t : Type) (x : myType2 t) : ∃ y : t, x = const3 y ∨ x = const4 y := by
  querySMT

set_option querySMT.filterRedundancies true in
example (t : Type) (x : myType2 t) : ∃ y : t, x = const3 y ∨ x = const4 y := by
  apply @Classical.byContradiction
  intro negGoal
  obtain ⟨_const3__sel0, _const3__sel0Fact⟩ :
    ∃ (_const3__sel0 : myType2 t → t), ∀ (arg0 : t), _const3__sel0 (const3 arg0) = arg0 :=
    by
    apply Exists.intro (rec (motive := fun (_ : myType2 t) => t) (fun (arg0 : t) => arg0) fun (arg0 : t) => sorry)
    intros
    rfl
  obtain ⟨_const4__sel0, _const4__sel0Fact⟩ :
    ∃ (_const4__sel0 : myType2 t → t), ∀ (arg0 : t), _const4__sel0 (const4 arg0) = arg0 :=
    by
    apply Exists.intro (rec (motive := fun (_ : myType2 t) => t) (fun (arg0 : t) => sorry) fun (arg0 : t) => arg0)
    intros
    rfl
  duper [negGoal, _const3__sel0Fact, _const4__sel0Fact] []

set_option pp.explicit true in
example (x y z : Int) : x ≤ y → y ≤ z → x ≤ z := by
  querySMT

example (f : Int → Int) (bv1 : ∀ x y, f x = f y → x = y)
(h2 : ∃ x, ∀ y, f x ≤ f y) : ∃ x, ∀ y, x ≠ y → f x < f y := by
  querySMT
  -- WITH REDUNDANCIES REMOVED, small problem, it needed an extra lemma
  -- apply @Classical.byContradiction
  -- intro negGoal
  -- skolemizeAll
  -- have smtLemma0 : ∀ (_i_0 : ℤ), ¬f sk0 + -Int.ofNat 1 * f _i_0 ≥ Int.ofNat 1 := by grind
  -- have smtLemma1 : ∀ (bv1 : ℤ), f bv1 + -Int.ofNat 1 * f (sk1 bv1) ≥ Int.ofNat 0 := by grind
  -- have smtLemma2 : ∀ (bv1 : ℤ), ¬bv1 = sk1 bv1 := by grind
  -- have smtLemma3 :
  --   (¬f sk0 + -Int.ofNat 1 * f (sk1 sk0) ≥ Int.ofNat 0 ∨ f sk0 = f (sk1 sk0)) ∨
  --     f sk0 + -Int.ofNat 1 * f (sk1 sk0) ≥ Int.ofNat 1 :=
  --   by grind
  -- duper [h1, smtLemma0, smtLemma1, smtLemma2, smtLemma3] []

example (f : Int → Int) (h1 : ∀ x y, f x = f y → x = y)
(h2 : ∃ x, ∀ y, f x ≤ f y) : ∃ x, ∀ y, x ≠ y → f x < f y := by
  apply @Classical.byContradiction
  intro negGoal
  skolemizeAll
  have smtLemma0 : ∀ (_i_0 : ℤ), ¬f sk0 + -Int.ofNat 1 * f _i_0 ≥ Int.ofNat 1 := by grind
  have smtLemma1 : ∀ (bv1 : ℤ), f bv1 + -Int.ofNat 1 * f (sk1 bv1) ≥ Int.ofNat 0 := by grind
  have smtLemma2 : ∀ (bv1 : ℤ), ¬bv1 = sk1 bv1 := by grind
  have smtLemma3 :
    (¬f sk0 + -Int.ofNat 1 * f (sk1 sk0) ≥ Int.ofNat 0 ∨ f sk0 = f (sk1 sk0)) ∨
      f sk0 + -Int.ofNat 1 * f (sk1 sk0) ≥ Int.ofNat 1 :=
    by grind
  duper [h1, smtLemma0, smtLemma1, smtLemma2, smtLemma3] []

example (f : Int → Int) (h1 : ∀ x y, f x = f y → x = y)
  (h2 : ∃ x, ∀ y, f x ≤ f y) : ∃ x, ∀ y, x ≠ y → f x < f y := by
  apply @Classical.byContradiction
  intro negGoal
  skolemizeAll
  have smtLemma0 : ∀ (_i_0 : Int), ¬f sk0 - f _i_0 ≥ 1 := by grind
  have smtLemma1 : ∀ (z : Int), f z - f (sk1 z) ≥ 0 := by grind
  have smtLemma2 :
    (¬f sk0 - f (sk1 sk0) ≥ 0 ∨ f sk0 = f (sk1 sk0)) ∨
    f sk0 - f (sk1 sk0) ≥ 1 := by grind
  duper [h1, h2, negGoal, smtLemma0, smtLemma1, smtLemma2] []

set_option querySMT.filterRedundancies false in
example (f : Int → Int) (h1 : ∀ x y, f x = f y → x = y)
(h2 : ∃ x, ∀ y, f x ≤ f y) : ∃ x, ∀ y, x ≠ y → f x < f y := by
  apply @Classical.byContradiction
  intro negGoal
  skolemizeAll
  have smtLemma0 : (∀ (_i_0 : ℤ), f sk0 ≤ f _i_0) → ∀ (_i_0 : ℤ), ¬f sk0 + -Int.ofNat 1 * f _i_0 ≥ Int.ofNat 1 := by
    grind
  have smtLemma1 :
    (∀ (_i : ℤ), ¬(¬_i = sk1 _i → f _i < f (sk1 _i))) →
      ∀ (bv1 : ℤ), f bv1 + -Int.ofNat 1 * f (sk1 bv1) ≥ Int.ofNat 0 :=
    by grind
  have smtLemma2 :
    (¬f sk0 + -Int.ofNat 1 * f (sk1 sk0) ≥ Int.ofNat 0 ∨ f sk0 = f (sk1 sk0)) ∨
      f sk0 + -Int.ofNat 1 * f (sk1 sk0) ≥ Int.ofNat 1 :=
    by grind
  duper [h1, h2, negGoal, smtLemma0, smtLemma1, smtLemma2] [] 
