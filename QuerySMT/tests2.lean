import QuerySMT
import Aesop

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


example (x y z : Int) : x < y → y < z → x < z := by
  querySMT

-- Simple Int Inequalities
example (x y z : Int) : x < y → y < z → x < z := by
  intros h0 h1
  apply @Classical.byContradiction
  intro negGoal
  have smtLemma0 : ¬x + -1 * y ≥ 0 := by grind
  have smtLemma1 : z + -1 * y ≥ 1 := by grind
  have smtLemma2 : x + -1 * z ≥ 0 := by grind
  have smtLemma3 : x + -1 * z ≥ 0 ∧ z + -1 * y ≥ 1 → x + -1 * y ≥ 0 := by grind
  duper [smtLemma0, smtLemma1, smtLemma2, smtLemma3] []

example (x y z : Int) : x < y → z < x → ¬z = y := by
  querySMT

example (w x y z : Int) : w <= x → x <= y → y <= z → z <= w → w = y := by
  querySMT

example (x y z : Int) : x <= y → y <= z → x = z → x = y ∧ y = z := by
  querySMT

example (x y z : Int) : x > y + z → x < y → z < 0 := by
  querySMT

-- Fails
-- example (f : Int → Int) (h1 : ∀ x y : Int, x < y → f x < f y) : ∀ x y : Int, x ≠ y → f x ≠ f y := by
--   querySMT

example (f : Int → Int) (h1 : ∀ x y : Int, f x + f y ≤ x + y) : f 0 = 0 → ∀ x : Int, f x ≤ x := by
  querySMT

example (f : Int → Int) (h1 : ∀ x y : Int, f x = f y → x = y) : ∀ x y : Int, x ≠ y → f x ≠ f y := by
  querySMT

-- Fails
-- example (f : Int → Int) (h1 : ∀ x y : Int, x < y → f x < f y) : ∀ x y : Int, f x = f y → x = y := by
--  querySMT

example (f g : Int → Int) (h1 : ∀ x : Int, f (g x) = x) : (∀ x y : Int, x ≠ y → g x ≠ g y) ∧ (∀ y : Int, ∃ x : Int, f x = y) := by
  querySMT

-- Simple Nat Inequalities
example (x y z : Nat) : x < y → y < z → x < z := by
  querySMT

-- This is an option for removing Int.ofNat in many places but I believe it to be worse
example (x y z : Nat) : x < y → y < z → x < z := by
  intros h0 h1
  apply @Classical.byContradiction
  intro negGoal
  have smtLemma0 : LT.lt (α := ℤ) ↑x ↑y → ¬↑x + -1 * Int.ofNat y ≥ 0 := by grind
  have smtLemma1 : LT.lt (α := ℤ) ↑y ↑z → ↑z + -1 * Int.ofNat y ≥ 1 := by grind
  have smtLemma2 : ¬LT.lt (α := ℤ) ↑x ↑z → ↑x + -1 * Int.ofNat z ≥ 0 := by grind
  have smtLemma3 : ↑x + -1 * Int.ofNat z ≥ 0 ∧ ↑z + -1 * Int.ofNat y ≥ 1 → ↑x + -1 * Int.ofNat y ≥ 0 := by grind
  duper [h0, h1, negGoal, smtLemma0, smtLemma1, smtLemma2, smtLemma3] [Int.ofNat_lt]

example (x y z : Nat) : x < y → z < x → ¬z = y := by
  querySMT

example (w x y z : Nat) : w <= x → x <= y → y <= z → z <= w → w = y := by
  querySMT

example (x y z : Nat) : x <= y → y <= z → x = z → x = y ∧ y = z := by
  querySMT

example (x y z : Nat) : x > y + z → x < y → z < 0 := by
  querySMT

-- Fails
-- example (f : Nat → Nat) (h1 : ∀ x y : Nat, x < y → f x < f y) : ∀ x y : Nat, x ≠ y → f x ≠ f y := by
--   querySMT

-- Fails
-- example (f : Nat → Nat) (h1 : ∀ x y : Nat, f x + f y ≤ x + y) : f 0 = 0 → ∀ x : Nat, f x ≤ x := by
--   querySMT

example (f : Nat → Nat) (h1 : ∀ x y : Nat, f x = f y → x = y) : ∀ x y : Nat, x ≠ y → f x ≠ f y := by
  querySMT

-- Fails
-- example (f : Nat → Nat) (h1 : ∀ x y : Nat, x < y → f x < f y) : ∀ x y : Nat, f x = f y → x = y := by
--   querySMT

example (f g : Nat → Nat) (h1 : ∀ x : Nat, f (g x) = x) : (∀ x y : Nat, x ≠ y → g x ≠ g y) ∧ (∀ y : Nat, ∃ x : Nat, f x = y) := by
  querySMT

-- Complex Algebraic Inequalities

-- Simple Arithmetic Possibility

-- Complex Arithmetic Possibility

-- List Lemmas

example (xs : List Unit) (x : Unit) : x::xs ≠ xs := by
  querySMT

-- Fails
-- example (x : Unit) (xs : List Unit) (ys : List Unit) : xs.length = ys.length → x::xs = x::ys := by
--   querySMT
