/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro h,
  change true → false at h,
  apply h,
  triv,
end

example : false → ¬ true :=
begin
  intro h,
  change true → false,
  intro h2,
  exact h,
end

example : ¬ false → true :=
begin
  intro h,
  triv,
end

example : true → ¬ false :=
begin
  intro h,
  change false → false,
  intro h2,
  exact h2,
end

example : false → ¬ P :=
begin
  intro h,
  change P → false,
  intro h2,
  exact h,
end

example : P → ¬ P → false :=
begin
  intro h,
  intro h2,
  change P → false at h2,
  apply h2,
  exact h,
end

example : P → ¬ (¬ P) :=
begin
  intro h,
  change ¬ (P → false),
  change (P → false) → false,
  intro h2,
  apply h2,
  exact h,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro h,
  intro h2,
  change P → false,
  intro h3,
  change Q → false at h2,
  apply h2,
  apply h,
  exact h3,
end

example : ¬ ¬ false → false :=
begin
  intro h,
  change ((false → false) → false) at h,
  apply h,
  intro h2,
  exact h2,
end

example : ¬ ¬ P → P :=
begin
  intro h,
  by_contra h2,
  apply h,
  exact h2,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros h hP,
  change (Q → false) → (P → false) at h,
  by_contra hnQ,
  apply h,
  exact hnQ,
  exact hP,
end