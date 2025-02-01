import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fin.VecNotation

open scoped BigOperators

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, DecidableEq (α i)]

namespace Finset

structure CombiDegen (φ ψ : List (∀ i, α i)) where
  u : ∀ i, α i → ℤ
  sum_eq_zero : ∀ x ∈ φ, ∑ i, u i (x i) = 0
  sum_pos : ∀ x ∈ ψ, 0 < ∑ i, u i (x i)

-- def IsCombiDegen (φ ψ : List (∀ i, α i)) : Prop :=
--   φ ⊆ ψ ∧ Nonempty (CombiDegen φ (ψ \ φ))

namespace F3

def φ : List (Fin 3 → Fin 9) :=
 [![0, 0, 0],
  ![1, 1, 1],
  ![2, 2, 2],
  ![3, 3, 3],
  ![4, 4, 4],
  ![7, 7, 7],
  ![8, 8, 8]]

def ψ : List (Fin 3 → Fin 9) :=
 [![5, 5, 5],
  ![6, 6, 6],
  ![0, 3, 1],
  ![0, 6, 2],
  ![1, 4, 2],
  ![1, 7, 0],
  ![2, 5, 0],
  ![2, 8, 1],
  ![3, 6, 4],
  ![3, 0, 5],
  ![4, 7, 5],
  ![4, 1, 3],
  ![5, 8, 3],
  ![5, 2, 4],
  ![6, 0, 7],
  ![6, 3, 8],
  ![7, 1, 8],
  ![7, 4, 6],
  ![8, 2, 6],
  ![8, 5, 7]]

def u : Fin 3 → Fin 9 → ℤ :=
  ![![-5, -5, -5, -5, -3, -1, -1, -3, -5],
    ![1, 4, 1, 5, 2, 5, 5, 2, 5],
    ![4, 1, 4, 0, 1, 5, 5, 1, 0]]

def combiDegen : CombiDegen φ ψ where
  u := u
  sum_eq_zero := by simp [φ]; decide
  sum_pos := by simp [ψ]; decide

end F3

namespace F2

def φ : List (Fin 3 → Fin 2 → Fin 4) :=
 [![![0, 0], ![0, 0], ![0, 0]],
  ![![0, 1], ![0, 1], ![0, 1]],
  ![![1, 0], ![1, 0], ![1, 0]],
  ![![1, 2], ![1, 2], ![1, 2]],
  ![![1, 3], ![1, 3], ![1, 3]],
  ![![2, 0], ![2, 0], ![2, 0]],
  ![![2, 1], ![2, 1], ![2, 1]],
  ![![2, 2], ![2, 2], ![2, 2]],
  ![![3, 1], ![3, 1], ![3, 1]],
  ![![3, 2], ![3, 2], ![3, 2]],
  ![![3, 3], ![3, 3], ![3, 3]]]

def ψ : List (Fin 3 → Fin 2 → Fin 4) :=
 [![![0, 2], ![0, 2], ![0, 2]],
  ![![0, 3], ![0, 3], ![0, 3]],
  ![![1, 1], ![1, 1], ![1, 1]],
  ![![2, 3], ![2, 3], ![2, 3]],
  ![![3, 0], ![3, 0], ![3, 0]],
  ![![0, 0], ![0, 2], ![0, 1]],
  ![![0, 0], ![2, 0], ![1, 0]],
  ![![0, 0], ![2, 2], ![1, 1]],
  ![![0, 1], ![0, 3], ![0, 0]],
  ![![0, 1], ![2, 1], ![1, 1]],
  ![![0, 1], ![2, 3], ![1, 0]],
  ![![0, 2], ![0, 0], ![0, 3]],
  ![![0, 2], ![2, 0], ![1, 3]],
  ![![0, 2], ![2, 2], ![1, 2]],
  ![![0, 3], ![0, 1], ![0, 2]],
  ![![0, 3], ![2, 1], ![1, 2]],
  ![![0, 3], ![2, 3], ![1, 3]],
  ![![1, 0], ![1, 2], ![1, 1]],
  ![![1, 0], ![3, 0], ![0, 0]],
  ![![1, 0], ![3, 2], ![0, 1]],
  ![![1, 1], ![1, 3], ![1, 0]],
  ![![1, 1], ![3, 1], ![0, 1]],
  ![![1, 1], ![3, 3], ![0, 0]],
  ![![1, 2], ![1, 0], ![1, 3]],
  ![![1, 2], ![3, 0], ![0, 3]],
  ![![1, 2], ![3, 2], ![0, 2]],
  ![![1, 3], ![1, 1], ![1, 2]],
  ![![1, 3], ![3, 1], ![0, 2]],
  ![![1, 3], ![3, 3], ![0, 3]],
  ![![2, 0], ![0, 0], ![3, 0]],
  ![![2, 0], ![0, 2], ![3, 1]],
  ![![2, 0], ![2, 2], ![2, 1]],
  ![![2, 1], ![0, 1], ![3, 1]],
  ![![2, 1], ![0, 3], ![3, 0]],
  ![![2, 1], ![2, 3], ![2, 0]],
  ![![2, 2], ![0, 0], ![3, 3]],
  ![![2, 2], ![0, 2], ![3, 2]],
  ![![2, 2], ![2, 0], ![2, 3]],
  ![![2, 3], ![0, 1], ![3, 2]],
  ![![2, 3], ![0, 3], ![3, 3]],
  ![![2, 3], ![2, 1], ![2, 2]],
  ![![3, 0], ![1, 0], ![2, 0]],
  ![![3, 0], ![1, 2], ![2, 1]],
  ![![3, 0], ![3, 2], ![3, 1]],
  ![![3, 1], ![1, 1], ![2, 1]],
  ![![3, 1], ![1, 3], ![2, 0]],
  ![![3, 1], ![3, 3], ![3, 0]],
  ![![3, 2], ![1, 0], ![2, 3]],
  ![![3, 2], ![1, 2], ![2, 2]],
  ![![3, 2], ![3, 0], ![3, 3]],
  ![![3, 3], ![1, 1], ![2, 2]],
  ![![3, 3], ![1, 3], ![2, 3]],
  ![![3, 3], ![3, 1], ![3, 2]]]

def index (x : Fin 2 → Fin 4) : Fin 16 := 4 * x 0 + x 1

def u : Fin 3 → Fin 16 → ℤ :=
  ![![-10, -10, 10, 10, -10, -8,   7,  1, -5, -6,   9, 10, -3, -8,  8,  9],
    ![  0,   0,  1,  1,   0, 10,   3,  5,  1,  1,   1,  3,  1,  1,  1, -1],
    ![ 10,  10, -1,  1,  10, 10, -10, -6,  4,  5, -10, -7, 10,  7, -9, -8]]

def combiDegen : CombiDegen φ ψ where
  u i := u i ∘ index
  sum_eq_zero := by simp [φ]; decide
  sum_pos := by simp [ψ]; decide

end F2
end Finset
