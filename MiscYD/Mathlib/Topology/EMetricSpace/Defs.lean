import Mathlib.Topology.EMetricSpace.Defs

/-!
# TODO

Fix the `EMetricSpace` docstring.
-/

namespace EMetric
variable {X : Type*} [EMetricSpace X] {x : X}

@[simp] lemma closedBall_zero : closedBall x 0 = {x} := by ext; simp

end EMetric
