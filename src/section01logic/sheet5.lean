/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  rw h,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro h,
  rw h,
  intro h2,
  rw h2,
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro hPeQ,
  intro hQeR,
  rw hPeQ,
  rw hQeR,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  intro hPaQ,
  cases hPaQ with hP hQ,
  split,
  exact hQ,
  exact hP,
  intro hQaP,
  cases hQaP with hQ hP,
  split,
  exact hP,
  exact hQ,
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  intro h,
  cases h with hPaQ hR,
  cases hPaQ with hP hQ,
  split,
  exact hP,
  split,
  exact hQ,
  exact hR,
  intro h,
  cases h with hP hQaR,
  cases hQaR with hQ hR,
  split,
  split,
  exact hP,
  exact hQ,
  exact hR,
end

example : P ↔ (P ∧ true) :=
begin
  split,
  intro hP,
  split,
  exact hP,
  triv,
  intro hPaT,
  cases hPaT with hP hT,
  exact hP,
end

example : false ↔ (P ∧ false) :=
begin
  split,
  intro hF,
  exfalso,
  exact hF,
  intro hPaF,
  cases hPaF with hP hF,
  exact hF,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intro hPeQ,
  intro hReS,
  split,
  rw hPeQ,
  rw hReS,
  intro h,
  exact h,
  rw hPeQ,
  rw hReS,
  intro h,
  exact h,
end

example : ¬ (P ↔ ¬ P) :=
begin
  sorry
end
