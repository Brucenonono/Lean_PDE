import Mathlib

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- move this construction into an earlier file and write some lemmas about it
noncomputable def NormedSpace.evalEquiv [FiniteDimensional ℝ E] : E ≃ₗ[ℝ] ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  let a : E ≃ₗ[ℝ] ((E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ) := Module.evalEquiv ℝ E
  let b : ((E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] ((E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) :=
    LinearEquiv.congrLeft ℝ ℝ LinearMap.toContinuousLinearMap
  let c : ((E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] ((E →L[ℝ] ℝ) →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  a.trans (b.trans c)

variable
  (u : E → ℝ)

#check fderiv ℝ u -- more commonly used in mathlib, more lemmas

variable (U : Set E)

variable (F : (E →L[ℝ] ℝ) × ℝ × E → ℝ)

-- we are interested in the following ODE
#check ∀ x ∈ U, F (fderiv ℝ u x, u x, x) = 0

variable [FiniteDimensional ℝ E]

-- adjust to be a vector
noncomputable abbrev DpF (X : (E →L[ℝ] ℝ) × ℝ × E) : E :=
  NormedSpace.evalEquiv.symm ((fderiv ℝ F X) ∘L ContinuousLinearMap.inl ℝ _ _)

-- adjust to be a real number
noncomputable abbrev DzF (X : (E →L[ℝ] ℝ) × ℝ × E) : ℝ :=
  (fderiv ℝ F X ∘L ContinuousLinearMap.inr ℝ _ _ ∘L ContinuousLinearMap.inl ℝ _ _) 1

noncomputable abbrev DxF (X : (E →L[ℝ] ℝ) × ℝ × E) : E →L[ℝ] ℝ :=
  fderiv ℝ F X ∘L ContinuousLinearMap.inr ℝ _ _ ∘L ContinuousLinearMap.inr ℝ _ _

-- let's write down the characteristic equations

variable (p : ℝ → (E →L[ℝ] ℝ)) (z : ℝ → ℝ)
  (x : ℝ → E) -- hopefully the output of the `x` function lives in `U`

/-- Property that the functions `p`, `z`, `x` satisfy the characteristic equations of `F` on the
interval `I`. -/
structure CharEqnSolution (I : Set ℝ) : Prop where
  eq_p : ∀ s ∈ I, deriv p s = - DxF F (p s, z s, x s) - DzF F (p s, z s, x s) • p s
  eq_z : ∀ s ∈ I, deriv z s = p s (DpF F (p s, z s, x s))
  eq_x : ∀ s ∈ I, deriv x s = DpF F (p s, z s, x s)
