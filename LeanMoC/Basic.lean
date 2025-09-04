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

variable (I : Set ℝ)

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



variable (p : ℝ → (E →L[ℝ] ℝ)) (z : ℝ → ℝ)
  (x : ℝ → E) (s : ℝ)-- hopefully the output of the `x` function lives in `U`

noncomputable def φ (x : E) : (E →L[ℝ] ℝ) × ℝ × E := (fderiv ℝ u x, u x, x)
noncomputable def G := F ∘ (φ u)

variable (hz : z = u ∘ x) (hp : ∀ s ∈ I, p s = fderiv ℝ u (x s))
variable (hDx : DifferentiableAt ℝ x s) (hDz : DifferentiableAt ℝ u (x s))
variable (hu : ContDiffOn ℝ 2 u U) (h_pde : ∀ y ∈ U, G y = 0)
-- variable (hF : F is C1 continuous on U)

#check DpF F (p s, z s, x s)
#check deriv p s
#check deriv x s
#check fderiv ℝ p s
#check fderiv ℝ u (x s)
#check p s
variable (I : Set ℝ)

-- Dxf = DpF Dxp + DzF Dxu + DxF = 0 ??
example :
  (fderiv ℝ (fun t => F (t, u (x s), x s)) (fderiv ℝ u (x s))) ∘ (fderiv ℝ (fderiv ℝ u) (x s)) +
    (fderiv ℝ (fun t => F (fderiv ℝ u (x s), t, (x s))) (u (x s))) ∘ (fderiv ℝ u (x s)) +
    (fderiv ℝ (fun t => F (fderiv ℝ u (x s), u (x s), t)) (x s)) = 0:=
  by

  have hG' : fderiv ℝ (G u F) (x s) = 0 := by
    sorry

  have hφ' : fderiv ℝ (φ u) (x s) =
    (fderiv ℝ (fderiv ℝ u) (x s)).prod ((fderiv ℝ u (x s)).prod (ContinuousLinearMap.id ℝ E)) := by
    sorry

  have hφ_diff : DifferentiableAt ℝ (φ u) (x s) := by
    sorry

  have hF_diff : DifferentiableAt ℝ F (φ u (x s)) := by
    sorry

  change fderiv ℝ (F ∘ φ u) (x s) = 0 at hG'
  rw [fderiv_comp (x s) (hF_diff) (hφ_diff)] at hG'
  rw [hφ'] at hG'

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

-- eq_p proof via substitution
example : fderiv ℝ p s = - (fderiv ℝ (fun t => F (fderiv ℝ u (x s), t, (x s))) (u (x s))) ∘ (fderiv ℝ u (x s)) -
    (fderiv ℝ (fun t => F (fderiv ℝ u (x s), u (x s), t)) (x s)) := by
  sorry


-- eq_z proof via substitution
example (heq_x : ∀ s, s ∈ I → deriv x s = DpF F (p s, z s, x s)) :
  ∀ s ∈ I, fderiv ℝ z s = (p s).comp (fderiv ℝ x s):= by
  intro s hs
  have chain_Dp : fderiv ℝ (u ∘ x) s = (fderiv ℝ u (x s)).comp (fderiv ℝ x s):= by
    exact fderiv_comp s hDz hDx
  rw[hz]
  rw[hp s hs] at chain_Dp

/-- suppose DDxu = Dxp, Dsx = DpF, DxF = 0,
substitute to get Dsp = Dxp DpF = -DzF Dxu -DxF
to show: D₁F(φ(x))∘t₁∘Dφ(x) = DDu(x(s))∘Dx(s) = Dₛp(s)
t₁∘Dφ(x) = DDu(x(s))
D₁F(φ(x) = Dx(s) by assumption
but can we reverse composition?
--/

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


variable (g : E → ℝ)

/-- compatibility condition-/
structure CompatSol (p0 : E)(z0 : ℝ)(x0 : E)where
  CondZ : z0 = g x0
  CondF : F


/-- noncharaceteristic boundary data-/

theorem NoncharBounCond
(hFpn : ) : (∃! q : E → E, ∃ 𝓝 x0, ∀ y ∈ 𝓝, ) := by
