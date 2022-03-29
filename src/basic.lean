import data.real.basic
import data.set.intervals.basic
import data.complex.exponential

noncomputable theory
open_locale classical

open set

example :( (1:ℝ) / 2) ∈ Icc (0 : ℝ) 1 :=
begin
  split;
  linarith,
end

namespace fuzzy

def fuzzy_set (u : Type) := u → Icc (0 : ℝ) 1

@[simp]
def mem {u : Type} (X : fuzzy_set u) (x : u) : ℝ := (X x).val

variable {u : Type}
variables (X Y : fuzzy_set u)

lemma mem_def : ∀ x, mem X x ∈ Icc (0:ℝ) 1 := λ x, (X x).2
lemma mem_pos : ∀ x, 0 ≤ mem X x := λ x, (X x).2.1
lemma mem_le_one : ∀ x, mem X x ≤ 1 := λ x, (X x).2.2

@[simp]
def support (X : fuzzy_set u) : set u := {x : u | (mem X x) > 0}

@[simp]
def classical_to_fuzzy (X : set u) : fuzzy_set u := λ x, ite (x ∈ X) ⟨1,by simp⟩ ⟨0,by simp⟩


example : mem (classical_to_fuzzy (Icc (3:ℝ) 5)) 4 ≥ 0.5 :=
begin
  have h1 : 3 ≤ (4 : ℝ) ∧ (4 : ℝ) ≤ 5, by {split; linarith},
  rw show mem (classical_to_fuzzy (Icc (3:ℝ) 5)) (4:ℝ) = 1, by simp [h1],
  linarith,
end


def test : fuzzy_set ℝ := λ x,
⟨(real.sin x)^2,by {split; nlinarith [real.neg_one_le_sin x, real.sin_le_one x]}⟩

-- Donat un conjunt fuzzy i un llindar α, construir el conjunt clàssic associat
-- x ∈ cl(X, α) ↔ mem X x > α

-- Enuncia i demostra el lema : si α ≤ β, cl(X, β) ⊆ cl(X, α)
end fuzzy