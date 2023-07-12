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

notation `ℱ` X  := classical_to_fuzzy X

example : mem (ℱ (Icc (3:ℝ) 5)) 4 ≥ 0.5 :=
begin
  have h1 : 3 ≤ (4 : ℝ) ∧ (4 : ℝ) ≤ 5, by {split; linarith},
  rw show mem (ℱ (Icc (3:ℝ) 5)) (4:ℝ) = 1, by simp [h1],
  linarith,
end


def test : fuzzy_set ℝ := λ x,
⟨(real.sin x)^2,by {split; nlinarith [real.neg_one_le_sin x, real.sin_le_one x]}⟩

-- Donat un conjunt fuzzy i un llindar α, construir el conjunt clàssic associat
-- x ∈ cl(X, α) ↔ mem X x > α

-- Enuncia i demostra el lema : si α ≤ β, cl(X, β) ⊆ cl(X, α)

instance {α : Type*} : has_sup (fuzzy_set α) := { sup := λ A B, (λ x, max (A x) (B x)) }
instance {α : Type*} : has_inf (fuzzy_set α) := { inf := λ A B, (λ x, max (A x) (B x)) }



@[norm_cast] lemma max_val_comm {x y : Icc (0 : ℝ) 1} :  ((max x y) : ℝ) = max x.val y.val :=
begin
  by_cases h : x ≤ y,
  {
    simp [h],
  },
  {
    replace h : y ≤ x,
    {
      unfold has_le.le,
      unfold preorder.le,
      push_neg at h,
      unfold has_lt.lt at h,
      unfold preorder.lt at h,
      linarith [h],
    },
    simp [h],
  }
end

instance is_lattice {α : Type*} : lattice (fuzzy_set α) := sorry

instance is_distrib_lattice {α : Type*} : distrib_lattice (fuzzy_set α) := {
  le_sup_inf := sorry
  ..fuzzy.is_lattice
}

example {a b : ℝ} (x : Icc a b) : (x : ℝ) ≤ b :=
begin
rcases x with ⟨xv, ⟨x1, x2⟩⟩,
norm_num,
exact x2,
end


#check Sup (range (mem X))

end fuzzy

variables (A : set ℝ)
#check (univ : set ℝ)

