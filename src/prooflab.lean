/-
When Lean starts, it automatically imports the contents of the library init folder, which includes a number of fundamental definitions and constructions. As a result, most of the examples we present here work “out of the box.”

If you want to use additional files, however, they need to be imported manually, via an import statement at the beginning of a file. 
-/
import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where
import topology.basic
--import topology.category.Top
--import category_theory.category.basic
import tactic.polyrith

namespace PROOFS

notation `fix ` binders `, ` r:(scoped f, f) := r


end PROOFS