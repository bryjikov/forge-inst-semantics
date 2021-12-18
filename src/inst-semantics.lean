import lovelib

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

structure sig := (name : name)

structure relation := (name : name) (sigs : list sig)

structure atom := (name : name) (sig : sig)

-- so that binds can take in sigs or relations
inductive atom_or_sig_or_rel : Type
| atom : atom → atom_or_sig_or_rel
| sig : sig → atom_or_sig_or_rel
| rel : relation → atom_or_sig_or_rel

def sig_bound := sig → list atom

structure sig_bounds :=
(lower : sig_bound)
(upper : sig_bound)

def rel_bound := relation → list (list atom)

structure rel_bounds :=
(lower : rel_bound)
(upper : rel_bound)

end LoVe
