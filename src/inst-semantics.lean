import lovelib

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

inductive sig : Type
| extend : name → sig → sig
| root : sig

inductive relation : Type
-- sigs are relations of arity 1
| sig : sig → relation
-- if you want a relation of arity more than 1
| rel : sig → relation → relation

inductive atom : Type
| atom : name → sig → atom

-- so that binds can take in sigs or relations
inductive atom_or_sig_or_rel : Type
| atom : atom → atom_or_sig_or_rel
| sig : sig → atom_or_sig_or_rel
| rel : relation → atom_or_sig_or_rel

end LoVe
