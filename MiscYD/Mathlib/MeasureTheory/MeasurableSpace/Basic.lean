import Mathlib.MeasureTheory.MeasurableSpace.Basic

namespace MeasureTheory

/-- Sigma-algebra generated by a random variable.

TODO: Generalise this notation to several variables. -/
scoped notation "σ(" X ")" => MeasurableSpace.comap X inferInstance

end MeasureTheory
