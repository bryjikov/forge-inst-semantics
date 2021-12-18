import lovelib

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

/-!
Is this the best way to do this?
I tried to do it this way to get
relations of any arity, but it does mean
that to construct a relation of many arity
you need to do
`relation (A → (relation B → (relation C → sig D)))`
or something like that
-/
inductive forge_rel (α β : Type) : Type → Type
| sig : forge_rel α
| relation : forge_rel (α → β)

/-!
In the semantics for bound_refinement from the paper,
do these take in two forge_rels?
can they take in atoms?
-/
inductive binding (α : Type) : Type
| and : α → α → binding
  --Lean has an `in` keyword
| inst_in : α → α → binding
| not_in : α → α → binding

inductive bounds 

end LoVe
