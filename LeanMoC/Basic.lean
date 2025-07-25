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

-- we are interested in the following PDE
#check ∀ x ∈ U, F (fderiv ℝ u x, u x, x) = 0

variable [FiniteDimensional ℝ E]

-- adjust to be a vector
noncomputable abbrev DpF (X : (E →L[ℝ] ℝ) × ℝ × E) : E :=
  NormedSpace.evalEquiv.symm ((fderiv ℝ F X) ∘L ContinuousLinearMap.inl ℝ _ _)

-- adjust to be a real number
noncomputable abbrev DzF (X : (E →L[ℝ] ℝ) × ℝ × E) : ℝ :=
  (fderiv ℝ F X ∘L ContinuousLinearMap.inr ℝ _ _ ∘L ContinuousLinearMap.inl ℝ _ _) 1
-- DF(X)[0,1,0] is the vector isomorphic to DzF(X)

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

variable (s : ℝ)
#check DpF F (p s, z s, x s)
#check deriv p s
#check deriv x s
#check fderiv ℝ p s
#check fderiv ℝ u (x s)
#check p s
variable (I : Set ℝ)

-- chain rule for z
example (hz : DifferentiableAt ℝ u (x s))  (hu : DifferentiableAt ℝ x s):
  fderiv ℝ (u ∘ x) s = (fderiv ℝ u (x s)).comp (fderiv ℝ x s):= by
  exact fderiv_comp s hz hu

-- eq_z proof via simple substitution
example (hf : ∀ s ∈ I, fderiv ℝ (u ∘ x) s = (fderiv ℝ u (x s)).comp (fderiv ℝ x s))
  (h1 : z = u ∘ x) (hp : ∀ s ∈ I, p s = fderiv ℝ u (x s)) :
  ∀ s ∈ I, fderiv ℝ z s = (p s).comp (fderiv ℝ x s):= by
  intro s hs
  rw[h1]
  rw[hf s hs]
  rw[hp s hs]

noncomputable def φ (x : E) : (E →L[ℝ] ℝ) × ℝ × E := (fderiv ℝ u x, u x, x)
noncomputable def f := F ∘ (φ u)
-- Dxf = DpF Dxp + DzF Dxu + DxF = 0 ??
#check φ u (x s)
example (F_fφ : f = F ∘ φ )
    (hF : DifferentiableAt ℝ F (φ u (x s)))
    (hp : DifferentiableAt ℝ p s)
    (hz : DifferentiableAt ℝ z s)
    (hf : DifferentiableAt ℝ x s)
    (hφ : DifferentiableAt ℝ φ (x s)):
  fderiv ℝ f (x s) = fderiv ℝ F (fderiv ℝ u (x s), u (x s), x s) ∘
  ((fderiv ℝ (fderiv ℝ u) (x s)).prod ((fderiv ℝ u (x s)).prod (ContinuousLinearMap.id ℝ E))) :=
  by
  have φ' : fderiv ℝ (φ) (x s) =
  (fderiv ℝ (fderiv ℝ u) (x s)).prod ((fderiv ℝ u (x s)).prod (ContinuousLinearMap.id ℝ E)) :=
  by
    sorry
  rw[← φ']
  -- f = F∘φ
  rw[F_fφ]
  exact fderiv_comp (x s) hF hφ
  sorry

-- chain rule for p, Dsp = DDxu Dsx
example (hp : ∀ s ∈ I, p s = fderiv ℝ u (x s)) (hs : s ∈ I) (hu : ContDiff ℝ 2 u):
  fderiv ℝ p s = (fderiv ℝ (fderiv ℝ u) (x s)).comp (fderiv ℝ x s):= by
  have hpx : p = (fderiv ℝ u) ∘ x := by
    sorry -- composite functions
  rw[hpx]
  apply fderiv_comp
  sorry
  sorry -- show C2 continuous


/-- suppose DDxu = Dxp, Dsx = DpF, DxF = 0,
substitute to get Dsp = Dxp DpF = -DzF Dxu -DxF --/


theorem CharEqnStructure
  (hz : ∀ s ∈ I, z s = u (x s)) (hp : ∀ s ∈ I, p s = fderiv ℝ u (x s))
  (F_0 : F (p s, z s, x s) = 0)
  (eq_x : ∀ s ∈ I, deriv x s = DpF F (p s, z s, x s)) :
  (∀ s ∈ I, deriv p s = - DxF F (p s, z s, x s) )
  ∧ (∀ s ∈ I, deriv z s = p s (DpF F (p s, z s, x s)) ) := by
  constructor
  have ez : z = u ∘ x := sorry
  sorry
  have Dzxs : deriv z = p s ∘ (deriv x) := sorry
  sorry
