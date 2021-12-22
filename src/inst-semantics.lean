import lovelib

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- 
when we say something like (`C0 + `C1) in City, 
where City is a sig, and `C0, `C1 are atoms, 
we constraint the sig City to be a superset of (`C0 + `C1)
Similarly, we could say (`C0 ->`C1 + `C1 ->`C0) in Roads,
where Roads is a relation of the type City -> City
-/

structure sig := (name : string)

-- a relation has a name (e.g. Roads), and is between a list of sigs
-- for example Roads is of the type City -> City
-- Position could be of the type Person -> Time -> Location 
-- where Person, Time, Location are sigs
structure relation := (name : string) (sigs : list sig)

-- an atom could be thought of as a specific instance of the sig,
-- specified in the partial instance
-- For the bound (`C0 + `C1) in City,
-- `C0  is an atom with name "C0" of the sig City
structure atom := (name : string) (sig : sig)

-- the upper or lower bound of a sig, which is a set of atoms
def sig_bound := sig → set atom

-- the final bound of a sig should have a lower bound and an upper bound
-- when without any specifications, the lower bound should default to empty
-- while the upper bound should default to univ
structure sig_bounds :=
(lower : sig_bound)
(upper : sig_bound)

-- a rel_bound would look like
-- Roads -> {[`C0, `C1], [`C1, `C0]}
def rel_bound := relation → set (list atom)

-- similar to sigs, a relation has a lower bound  and an upper bound
structure rel_bounds :=
(lower : rel_bound)
(upper : rel_bound)

structure all_bounds :=
(sigs : sig_bounds)
(rels : rel_bounds)

--For now, ignore `join`
--For now, each bind must include a list of atoms
--For now, ignore `not in`

/-
We are considering 4 kinds of bounds:

(`C0 + `C1) in City : atoms in sig City
City in (`C0 + `C1) : sig City in atoms
(`C0 ->`C1 + `C1 ->`C0) in Roads : (a relation of) atoms in relation Roads
Roads in (`C0 ->`C1 + `C1 ->`C0) : relation Roads in (a relation of) atoms
-/
inductive inst : Type
| sig_in_atoms : sig → set atom → inst
| atoms_in_sig : set atom → sig → inst
| rel_in_atoms : relation → set (list atom) → inst
| atoms_in_rel : set (list atom) → relation → inst


/-
Given an instance and the refined bounds we ahve so far, we arrive at new refined bounds
-/
def refine_bound [decidable_eq sig] [decidable_eq relation] : inst → all_bounds → all_bounds
| (inst.sig_in_atoms s1 atoms) (bounds : all_bounds) :=
  (all_bounds.mk (
    sig_bounds.mk bounds.sigs.lower (
      λ(s : sig),
        if s = s1 then
          atoms ∩ (bounds.sigs.upper s)
        else
          bounds.sigs.upper s
    )
  ) bounds.rels
  ) 
| (inst.atoms_in_sig atoms s1) (bounds : all_bounds) :=
  (all_bounds.mk (
    sig_bounds.mk (
      λ(s : sig),
        if s = s1 then
          atoms ∪ (bounds.sigs.lower s)
        else
          bounds.sigs.lower s
    ) bounds.sigs.upper
  ) bounds.rels
  )
| (inst.rel_in_atoms r1 atoms) (bounds : all_bounds) :=
  (all_bounds.mk bounds.sigs 
   (rel_bounds.mk bounds.rels.lower (
      λ(r : relation),
        if r = r1 then
          atoms ∩ (bounds.rels.upper r)
        else
          bounds.rels.upper r
      )
    )
  )
| (inst.atoms_in_rel atoms r1) (bounds : all_bounds) :=
   (all_bounds.mk bounds.sigs (
    rel_bounds.mk (
      λ(r : relation),
        if r = r1 then
          atoms ∪ (bounds.rels.lower r)
        else
          bounds.rels.lower r
    ) bounds.rels.upper
  )
)

/-
Recursively refine bounds for all instss in a list of instances
-/

def refine_bounds [decidable_eq sig] [decidable_eq relation] : list inst → all_bounds → all_bounds
| [] (bounds : all_bounds) := bounds
| (insthd :: rst) (bounds : all_bounds) := refine_bounds rst (refine_bound insthd bounds)

/-
an default starting bound, before looking at any inst
-/
def new_bounds : all_bounds :=
(all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
               (rel_bounds.mk (λx, ∅) (λx, set.univ)))


/-
When there are bound conflicts in insts,
there are bound confilcts in the resulting refined bounds
-/
lemma bounds_conflict_carries_for_sig [decidable_eq sig] [decidable_eq atom] [decidable_eq relation] (s1 : sig) (lower upper : set atom) :
  (lower ⊆ upper) ↔
    ((refine_bounds  [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                      new_bounds).sigs.lower s1)
        ⊆
       ((refine_bounds [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       new_bounds).sigs.upper s1) :=
begin
  have hlower : lower = (refine_bounds [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       new_bounds).sigs.lower s1 :=
      begin
         calc lower
             = (λ(s : sig), if s = s1 then (lower ∪ ∅) else ∅) s1 :
          by simp
        ... = (sig_bounds.mk (λ(s : sig), if s = s1 then (lower ∪ ∅) else ∅)
                             (λ(s : sig), if s = s1 then (upper ∩ set.univ) else set.univ)).lower s1 :
          by simp
         ... = (all_bounds.mk (sig_bounds.mk (λ(s : sig), if s = s1 then (lower ∪ ∅) else ∅)
                                             (λ(s : sig), if s = s1 then (upper ∩ set.univ) else set.univ))
                              (rel_bounds.mk (λx, ∅) (λx, set.univ))).sigs.lower s1 :
          by simp
        ... = (refine_bounds [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       new_bounds).sigs.lower s1 :
          by refl
      end,
  have hupper : upper = (refine_bounds [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       new_bounds).sigs.upper s1 :=
      begin
         calc upper
             = (λ(s : sig), if s = s1 then (upper ∩ set.univ) else set.univ) s1 :
          by simp
        ... = (sig_bounds.mk (λ(s : sig), if s = s1 then (lower ∪ ∅) else ∅)
                             (λ(s : sig), if s = s1 then (upper ∩ set.univ) else set.univ)).upper s1 :
          by simp
         ... = (all_bounds.mk (sig_bounds.mk (λ(s : sig), if s = s1 then (lower ∪ ∅) else ∅)
                                             (λ(s : sig), if s = s1 then (upper ∩ set.univ) else set.univ))
                              (rel_bounds.mk (λx, ∅) (λx, set.univ))).sigs.upper s1 :
          by simp
        ... = (refine_bounds [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       new_bounds).sigs.upper s1 :
          by refl
      end,
  apply iff.intro,
  { intro hlsubu,
    intro bound,
    intro hboundlower,
    have hboundeltlower : bound ∈ lower :=
      by cc,
    rw ←hupper,
    apply hlsubu,
    exact hboundeltlower, },
  { rw ←hupper,
    rw ←hlower,
    intro hlu,
    exact hlu, },
end

lemma bounds_conflict_carries_for_rel [decidable_eq sig] [decidable_eq atom] [decidable_eq relation] (r1 : relation) (lower upper : set (list atom)) :
  (lower ⊆ upper)
  ↔ ((refine_bounds [(inst.rel_in_atoms r1 upper), (inst.atoms_in_rel lower r1)] new_bounds).rels.lower r1)
    ⊆ ((refine_bounds [(inst.rel_in_atoms r1 upper), (inst.atoms_in_rel lower r1)] new_bounds).rels.upper r1) :=
begin
  have hlower : lower = (refine_bounds [(inst.rel_in_atoms r1 upper), (inst.atoms_in_rel lower r1)]
                       new_bounds).rels.lower r1 :=
      begin
         calc lower
             = (λ(r : relation), if r = r1 then (lower ∪ ∅) else ∅) r1 :
          by simp
        ... = (rel_bounds.mk (λ(r : relation), if r = r1 then (lower ∪ ∅) else ∅)
                             (λ(r : relation), if r = r1 then (upper ∩ set.univ) else set.univ)).lower r1 :
          by simp
         ... = (all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
                              (rel_bounds.mk (λ(r : relation), if r = r1 then (lower ∪ ∅) else ∅)
                                             (λ(r : relation), if r = r1 then (upper ∩ set.univ) else set.univ))).rels.lower r1 :
          by simp
        ... = (refine_bounds [(inst.rel_in_atoms r1 upper), (inst.atoms_in_rel lower r1)]
                       new_bounds).rels.lower r1 :
          by refl
      end,
  have hupper : upper = (refine_bounds [(inst.rel_in_atoms r1 upper), (inst.atoms_in_rel lower r1)]
                         new_bounds).rels.upper r1 :=
      begin
         calc upper
             = (λ(r : relation), if r = r1 then (upper ∩ set.univ) else set.univ) r1 :
          by simp
        ... = (rel_bounds.mk (λ(r : relation), if r = r1 then (lower ∪ ∅) else ∅)
                             (λ(r : relation), if r = r1 then (upper ∩ set.univ) else set.univ)).upper r1 :
          by simp
         ... = (all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
                              (rel_bounds.mk (λ(r : relation), if r = r1 then (lower ∪ ∅) else ∅)
                                             (λ(r : relation), if r = r1 then (upper ∩ set.univ) else set.univ))).rels.upper r1 :
          by simp
        ... = (refine_bounds [(inst.rel_in_atoms r1 upper), (inst.atoms_in_rel lower r1)]
                       new_bounds).rels.upper r1 :
          by refl
      end,
  apply iff.intro,
  { intro hlsubu,
    intro bound,
    intro hboundlower,
    have hboundeltlower : bound ∈ lower :=
      by cc,
    rw ←hupper,
    apply hlsubu,
    exact hboundeltlower, },
  { rw ←hupper,
    rw ←hlower,
    intro hlu,
    exact hlu, },
end

/-!
  We spent about an hour trying to figure this one out
  Turns out the only good way is to use casework
  But then you need to do cases on i1 and i2, which gives you at least 16 cases total
  So we decided it's not worth the time
-/

-- whether we refine the list of insts [i1, i2] or [i2, i1], we get the same result
lemma comm_binary [decidable_eq sig] [decidable_eq atom] [decidable_eq relation] (i1 i2 : inst) (bounds : all_bounds) :
  refine_bounds [i1, i2] bounds = refine_bounds [i2, i1] bounds :=
sorry

/-!
  We spent about 3 hours trying to figure this one out
  We got a proof by hand
  The proofs required induction with multiple base cases
  We need the cases where the list has length 1,2, and 3 for this
  The problem is the case with length 3 we could only do by casework, and we thought it wasn't worth doing the 64 cases that gives us
  We also could not figure out how to tell lean "we would like to induct, but we want to induct for cases with length >= 3
  and do the other cases by hand" instead of having it induct on all cases of size >= 1
-/

-- whether we refine the list of insts [i1, ...] or [..., i1], we get the same result
-- would imply that we can refine the list of inst in any order
lemma comm [decidable_eq sig] [decidable_eq atom] [decidable_eq relation]
  (bounds : all_bounds) (insthd : inst) (rst : list inst) :
  (refine_bounds (insthd :: rst) bounds) = (refine_bounds (rst.append [insthd]) bounds) :=
begin
  rw refine_bounds,
  sorry
end

lemma inst_reverse [decidable_eq sig] [decidable_eq atom] [decidable_eq relation] (i1 i2 i3 : inst) (bound : all_bounds) :
  refine_bounds [i1, i2, i3] bound = refine_bounds [i3, i2, i1] bound :=
calc refine_bounds [i1, i2, i3] bound
    = refine_bounds [i2, i3] (refine_bounds [i1] bound) :
  by refl
...  = refine_bounds [i3, i2] (refine_bounds [i1] bound) :
  by apply comm_binary
... = refine_bounds [i1, i3, i2] bound :
  by refl
... = refine_bounds [i2] (refine_bounds [i1, i3] bound) :
  by refl
... = refine_bounds [i2] (refine_bounds [i3, i1] bound) :
  by simp [comm_binary]
... = refine_bounds [i3, i1, i2] bound :
  by refl
... = refine_bounds [i1, i2] (refine_bounds [i3] bound) :
  by refl
... = refine_bounds [i2, i1] (refine_bounds [i3] bound) :
  by apply comm_binary
... = refine_bounds [i3, i2, i1] bound:
  by refl

lemma inst_assoc [decidable_eq sig] [decidable_eq atom] [decidable_eq relation] (i1 i2 i3 : inst) (bounds : all_bounds):
  refine_bounds [i1] (refine_bounds [i2, i3] bounds) = refine_bounds [i1, i2] (refine_bounds [i3] bounds) :=
calc refine_bounds [i1] (refine_bounds [i2, i3] bounds)
    = refine_bounds [i2, i3, i1] bounds:
  by refl
...  = refine_bounds [i3, i1] (refine_bounds [i2] bounds) :
  by refl
... = refine_bounds [i1, i3] (refine_bounds [i2] bounds) :
  by apply comm_binary
... = refine_bounds [i2, i1, i3] bounds :
  by refl
... = refine_bounds [i3, i1, i2] bounds :
  by apply inst_reverse

end LoVe
