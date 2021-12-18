import lovelib

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

structure sig := (name : name)

structure relation := (name : name) (sigs : list sig)

structure atom := (name : name) (sig : sig)

def sig_bound := sig → list atom

structure sig_bounds :=
(lower : sig_bound)
(upper : sig_bound)

def rel_bound := relation → list (list atom)

structure rel_bounds :=
(lower : rel_bound)
(upper : rel_bound)

structure all_bounds :=
(sigs : sig_bounds)
(rels : rel_bounds)

--For now, ignore join
--For now, each bind must include a list of atoms
inductive inst : Type
| and : inst → inst → inst
| sig_in_atoms : sig → list atom → inst
| atoms_in_sig : list atom → sig → inst
| rel_in_atoms : relation → list atom → inst
| atoms_in_rel : list atom → relation → inst

def refine_bounds : inst → all_bounds → all_bounds
| (inst.and i1 i2) (bounds : all_bounds) := refine_bounds i2 (refine_bounds i1 bounds)
| (inst.sig_in_atoms) (bounds : all_bounds) := ....

end LoVe
