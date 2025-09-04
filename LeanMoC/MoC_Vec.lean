import Mathlib

variable (n : ℕ)
variable (Ω : Set (Fin n → ℝ))
variable (E : Set (Fin n → ℝ))
def boundary_set (E : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x ∈ E | x (Fin.last (n-1)) = 0}

#check Fin.last 2
variable (F : (Fin n → ℝ) × ℝ × (Fin n → ℝ) → ℝ) -- Fin n → ℝ is n-D vector
def BoundaryHyperplane () : Set (Fin n → ℝ) :=
  {x | x (Fin.last n) = 0}

variable (g : (Fin n → ℝ) → ℝ)
variable (u : (Fin n → ℝ) → ℝ)

def CompatibilityCondition : Prop :=
  ∀ x ∈ BoundaryHyperplane n, u x = g x

#check fderiv ℝ F

structure AdmissibleTriple : Type where
  -- Initial solution value: z₀ = g(x₀)
  x₀ : Fin n → ℝ
  z₀ : ℝ := g x₀
  p₀ : Fin n → ℝ
  -- Initial gradient components: ∂u/∂xᵢ(x₀) = ∂g/∂xᵢ(x₀) for i = 1, ..., n-1
  Initial_Gradient : ∀ i : Fin n, i.val < n - 1 → -- i is index
    p₀ i = fderiv ℝ g x₀ (Pi.single i 1)
  -- Compatibility condition: F(x₀, g(x₀), p₀) = 0
  PDE_Compatibility : F (x₀, z₀, p₀) = 0

section
variable (p₀ : Fin n → ℝ) (z₀ : ℝ) (x₀ : Fin n → ℝ)
#check fderiv ℝ (fun t => F (t, z₀, x₀)) p₀
#check fun i => if i = n then 1 else 0
#check (fderiv ℝ (fun t => F (t, z₀, x₀)) p₀) (fun i => if i = n then 1 else 0) --partial derivative
end

variable (triple : AdmissibleTriple n F g)
-- if ∂F/∂pₙ ≠ 0
-- exist unique function q, st ∀ y near x, (q y, g y, y) is admissible

theorem NoncharBoundaryCondition (Initial_Tripple : AdmissibleTriple n F g)
(nonchar :
  let x₀ := Initial_Tripple.x₀
  let p₀ := Initial_Tripple.p₀
  let z₀ := Initial_Tripple.z₀
  (fderiv ℝ (fun t => F (t, z₀, x₀)) p₀) (fun i => if i = n then 1 else 0) ≠ 0) :
    ∃! q : (Fin n → ℝ) → (Fin n → ℝ), ∃ U ∈ 𝓝 x₀, ∀ y ∈ U, AdmissibleTriple {(q y), (g y), y}:=
  { p₀_normal := q x₀,
    pde_compatibility := (q_spec x₀).1,
    non_characteristic := (q_spec x₀).2 }
