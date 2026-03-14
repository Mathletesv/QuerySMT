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


-- Simple Int Inequalities
example (x y z : Int) : x < y → y < z → x < z := by
  querySMT

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
--  querySMT

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

-- Complex Algebraic Inequalities

-- Simple Arithmetic Possibility

-- Complex Arithmetic Possibility
