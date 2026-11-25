module

public import Solution

/-!
# Axiom audit for Erdős 963, part i

Building this file prints the axioms used by the main theorem and by the two explicit bounds.
The expected output is `[propext, Classical.choice, Quot.sound]` for each of them.
-/

#print axioms Erdos963.erdos_963.parts.i
#print axioms Erdos963.f_isEquivalent_logb
#print axioms Erdos963.f_upper
#print axioms Erdos963.f_lower
