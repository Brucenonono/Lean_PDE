import Mathlib

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (E) in
abbrev timesℝ : Type := WithLp 2 (E × ℝ)

postfix:max "xℝ" => timesℝ

variable
  (u : E xℝ → ℝ)

#check fderiv ℝ u -- more commonly used in mathlib, more lemmas
#check gradient u -- easier to visualize

-- for now let's try with `gradient`, might switch later

variable (U : Set (E xℝ))

variable (F : (E xℝ) × ℝ × (E xℝ) → ℝ)

-- we are interested in the following ODE
#check ∀ x ∈ U, F (gradient u x, u x, x) = 0

-- let's write down the characteristic equations

variable (p : ℝ → E xℝ) (z : ℝ → ℝ)
  (x : ℝ → E xℝ) -- hopefully the output of the `x` function lives in `U`

variable (x₀ : E xℝ)
#check (gradient F x₀).1 -- D_pF in Evans
