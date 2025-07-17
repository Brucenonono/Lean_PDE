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

variable (U : Set ((E xℝ)))

variable (F : (E xℝ) × ℝ × (E xℝ) → ℝ)

-- we are interested in the following ODE
#check ∀ x ∈ U, F (gradient u x, u x, x) = 0


-- adjust to be a vector
noncomputable abbrev DpF (X : E xℝ × ℝ × E xℝ) : (E xℝ) →L[ℝ] ℝ :=
  fderiv ℝ F X ∘L ContinuousLinearMap.inl ℝ _ _

-- adjust to be a real number
noncomputable abbrev DzF (X : E xℝ × ℝ × E xℝ) : ℝ :=
  (fderiv ℝ F X ∘L ContinuousLinearMap.inr ℝ _ _ ∘L ContinuousLinearMap.inl ℝ _ _) 1

-- adjust to be a vector
noncomputable abbrev DxF (X : E xℝ × ℝ × E xℝ) : (E xℝ) →L[ℝ] ℝ :=
  fderiv ℝ F X ∘L ContinuousLinearMap.inr ℝ _ _ ∘L ContinuousLinearMap.inr ℝ _ _

-- let's write down the characteristic equations

variable (p : ℝ → E xℝ) (z : ℝ → ℝ)
  (x : ℝ → E xℝ) -- hopefully the output of the `x` function lives in `U`

/-- Property that the functions `p`, `z`, `x` satisfy the characteristic equations of `F` on the
interval `I`. -/
structure CharEqnSolution (I : Set ℝ) : Prop where
  eq_p : ∀ s ∈ I, deriv p s = - (InnerProductSpace.toDual ℝ _).symm (DxF F (p s, z s, x s)) - DzF F (p s, z s, x s) • p s
  eq_z : ∀ s ∈ I, deriv z s = DpF F (p s, z s, x s) (p s)
  eq_x : ∀ s ∈ I, deriv x s = (InnerProductSpace.toDual ℝ _).symm (DpF F (p s, z s, x s))
