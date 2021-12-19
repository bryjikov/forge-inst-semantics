import lovelib

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

structure sig := (name : string)

structure relation := (name : string) (sigs : list sig)

structure atom := (name : string) (sig : sig)

def sig_bound := sig → set atom

structure sig_bounds :=
(lower : sig_bound)
(upper : sig_bound)

def rel_bound := relation → set (list atom)

structure rel_bounds :=
(lower : rel_bound)
(upper : rel_bound)

structure all_bounds :=
(sigs : sig_bounds)
(rels : rel_bounds)

--For now, ignore `join`
--For now, each bind must include a list of atoms
--For now, ignore `not in`
inductive inst : Type
| sig_in_atoms : sig → set atom → inst
| atoms_in_sig : set atom → sig → inst
| rel_in_atoms : relation → set (list atom) → inst
| atoms_in_rel : set (list atom) → relation → inst

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

def refine_bounds [decidable_eq sig] [decidable_eq relation] : list inst → all_bounds → all_bounds
| [] (bounds : all_bounds) := bounds
| (insthd :: rst) (bounds : all_bounds) := refine_bounds rst (refine_bound insthd bounds)

lemma bounds_conflict_carries_for_sig [decidable_eq sig] [decidable_eq atom] [decidable_eq relation] (s1 : sig) (lower upper : set atom) :
  (lower ⊆ upper) ↔
    ((refine_bounds  [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       (all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
                                      (rel_bounds.mk (λx, ∅) (λx, set.univ)))).sigs.lower s1)
        ⊆
       ((refine_bounds [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       (all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
                                      (rel_bounds.mk (λx, ∅) (λx, set.univ)))).sigs.upper s1) :=
begin
  have hlower : lower = (refine_bounds [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       (all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
                                      (rel_bounds.mk (λx, ∅) (λx, set.univ)))).sigs.lower s1 :=
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
                       (all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
                                      (rel_bounds.mk (λx, ∅) (λx, set.univ)))).sigs.lower s1 :
          by refl
      end,
  have hupper : upper = (refine_bounds [(inst.sig_in_atoms s1 upper), (inst.atoms_in_sig lower s1)]
                       (all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
                                      (rel_bounds.mk (λx, ∅) (λx, set.univ)))).sigs.upper s1 :=
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
                       (all_bounds.mk (sig_bounds.mk (λx, ∅) (λx, set.univ))
                                      (rel_bounds.mk (λx, ∅) (λx, set.univ)))).sigs.upper s1 :
          by refl
      end,
  apply iff.intro,
  { intro hlsubu,
    intro bound,
    intro hboundlower,
    simp [refine_bounds],
    simp,
    have hboundeltlower : bound ∈ lower :=
      by cc,
    apply hlsubu,
    exact hboundeltlower, },
  { rw ←hupper,
    rw ←hlower,
    intro hlu,
    exact hlu, },
end

lemma comm_binary [decidable_eq sig] [decidable_eq atom] [decidable_eq relation]
  (bounds : all_bounds) (a : inst) (b : inst) :
  (refine_bounds [a, b] bounds) = (refine_bounds [b, a] bounds) :=
begin
  
  sorry
  
end

lemma comm [decidable_eq sig] [decidable_eq atom] [decidable_eq relation]
  (bounds : all_bounds) (insthd : inst) (rst : list inst) :
  (refine_bounds (insthd :: rst) bounds) = (refine_bounds (rst.append [insthd]) bounds) :=
begin
  rw refine_bounds,
  sorry
end

end LoVe
