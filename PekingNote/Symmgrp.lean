import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating

abbrev Symmgrp (α : Type) := Equiv.Perm α

#check alternatingGroup
#check Fintype.card_perm
#check alternatingGroup.normal
