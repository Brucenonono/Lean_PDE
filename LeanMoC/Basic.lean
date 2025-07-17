import Mathlib

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "E'" => WithLp 2 (E × ℝ)

variable
  (u : E' → ℝ)

#check fderiv ℝ u -- more commonly used in mathlib, more lemmas
#check gradient u -- easier to visualize

-- for now let's try with `gradient`, might switch later

variable (U : Set E')

variable (F : E' × ℝ × E' → ℝ)

-- we are interested in the following ODE
#check ∀ x ∈ U, F (gradient u x) (u x) x = 0

-- let's write down the characteristic equations

variable (p : ℝ → E') (z : ℝ → ℝ)
  (x : ℝ → E') -- hopefully the output of the `x` function lives in `U`

variable (x₀ : E')
#check (gradient F x₀).1 -- D_pF in Evans
