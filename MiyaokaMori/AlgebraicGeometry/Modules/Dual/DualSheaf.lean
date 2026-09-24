import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualPresheafSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame

/-! # The dual sheaf without sheafification

The dual sheaf `dualSheaf M` of a sheaf of modules `M`, **without sheafification**: `Γ(U, M^∨)` is by
definition the set of compatible families of local functionals `LocalDualSections X M U` (for every
open `V ⊆ U` a `Γ(X,V)`-linear map `Γ(M,V) → Γ(X,V)`, compatible with restriction); the sheaf
condition is `moduleDualPresheaf_isSheaf`. The pairing `dualPair φ h x ∈ Γ(X, V)` (`V ≤ U`) is
linear and compatible with restriction. When `M` has a frame `e`, the dual frame `IsFrame.dualFrame`
is `x ↦ coord_e(x)`, with `⟨e^∨, e⟩ = 1`.

Design: `Scheme.Modules.dual M = moduleSheafDual M` sheafifies the same presheaf once more, so its
sections are only reachable through the sheafification unit and cannot be unfolded (this affects
`canonicalSection`, `contraction`, `coevSection`). Since the presheaf is already a sheaf, packaging it
directly makes the value of a section `rfl`. The isomorphism with `Scheme.Modules.dual` is in
`DualSheafOld` (the sheafification unit is an isomorphism).

References: Stacks 01CM (internal Hom), 01CR.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- The dual sheaf `M^∨ = 𝓗om(M, O_X)`, whose sections are compatible families of local functionals;
no sheafification. -/
def dualSheaf (M : X.Modules) : X.Modules where
  val := AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf M
  isSheaf := AlgebraicGeometry.Scheme.Modules.ModuleDualPresheafSheaf.moduleDualPresheaf_isSheaf M

/-- The elements of `Γ(U, M^∨)` are the compatible families of local functionals (the identity, `rfl`). -/
def dualSheafSections (M : X.Modules) (U : X.Opens) :
    Γ(dualSheaf M, U) ≃ₗ[Γ(X, U)] AlgebraicGeometry.Scheme.Modules.LocalDualSections X M U :=
  LinearEquiv.refl _ _

/-- The pairing: `φ ∈ Γ(U, M^∨)`, `V ≤ U`, `x ∈ Γ(V, M) ↦ φ(x) ∈ Γ(V, O_X)`. -/
def dualPair {M : X.Modules} {U : X.Opens} (φ : Γ(dualSheaf M, U)) {V : X.Opens} (h : V ≤ U) :
    Γ(M, V) →ₗ[Γ(X, V)] Γ(X, V) :=
  (dualSheafSections M U φ).1 (Over.mk (homOfLE h))

/-- The pairing commutes with restriction of `M` (compatibility). -/
theorem dualPair_res {M : X.Modules} {U : X.Opens} (φ : Γ(dualSheaf M, U)) {V' V : X.Opens}
    (h' : V' ≤ V) (h : V ≤ U) (x : Γ(M, V)) :
    dualPair φ (h'.trans h) (M.res h' x) = X.presheaf.map (homOfLE h').op (dualPair φ h x) :=
  (dualSheafSections M U φ).2 (Over.mk (homOfLE (h'.trans h))) (Over.mk (homOfLE h))
    (Over.homMk (homOfLE h')) x

/-- A section of the dual sheaf is determined by all its pairings. -/
theorem dualSheaf_ext {M : X.Modules} {U : X.Opens} {φ ψ : Γ(dualSheaf M, U)}
    (hφ : ∀ (V : X.Opens) (h : V ≤ U), dualPair φ h = dualPair ψ h) : φ = ψ := by
  apply (dualSheafSections M U).injective
  apply Subtype.ext
  funext V
  exact hφ V.left (leOfHom V.hom)

/-- Restriction of a section of the dual sheaf leaves the pairings unchanged. -/
theorem dualPair_res_left {M : X.Modules} {U' U : X.Opens} (hU : U' ≤ U) (φ : Γ(dualSheaf M, U))
    {V : X.Opens} (h : V ≤ U') :
    dualPair ((dualSheaf M).res hU φ) h = dualPair φ (h.trans hU) := rfl

@[simp] theorem dualPair_add {M : X.Modules} {U : X.Opens} (φ ψ : Γ(dualSheaf M, U)) {V : X.Opens}
    (h : V ≤ U) (x : Γ(M, V)) : dualPair (φ + ψ) h x = dualPair φ h x + dualPair ψ h x := rfl

@[simp] theorem dualPair_smul {M : X.Modules} {U : X.Opens} (r : Γ(X, U)) (φ : Γ(dualSheaf M, U))
    {V : X.Opens} (h : V ≤ U) (x : Γ(M, V)) :
    dualPair (r • φ) h x = X.presheaf.map (homOfLE h).op r * dualPair φ h x := rfl

/-- The dual frame `e^∨`: `x ↦` the coordinate of `x` in the frame `e`. -/
def IsFrame.dualFrame {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    Γ(dualSheaf M, W) :=
  (dualSheafSections M W).symm
    ⟨fun V => (hf.coordEquiv (leOfHom V.hom)).toLinearMap, by
      intro V V' i x
      exact hf.coord_map (leOfHom i.left) (leOfHom V'.hom) x⟩

@[simp] theorem IsFrame.dualPair_dualFrame {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {V : X.Opens} (h : V ≤ W) (x : Γ(M, V)) :
    dualPair hf.dualFrame h x = hf.coord h x := rfl

/-- A section of the dual sheaf is determined by its value on a frame: `φ = φ(e) • e^∨`. -/
theorem IsFrame.eq_smul_dualFrame {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e)
    {W' : X.Opens} (h : W' ≤ W) (φ : Γ(dualSheaf M, W')) :
    dualPair φ le_rfl (M.res h e) • (dualSheaf M).res h hf.dualFrame = φ := by
  apply dualSheaf_ext
  intro V hV
  apply LinearMap.ext
  intro x
  rw [dualPair_smul, dualPair_res_left, IsFrame.dualPair_dualFrame]
  have hx := hf.coord_smul_frame (hV.trans h) x
  conv_rhs => rw [← hx, LinearMap.map_smul]
  rw [← res_res M hV h e, dualPair_res φ hV le_rfl, smul_eq_mul, mul_comm]

/-- The dual frame is a frame of the dual sheaf; in particular the dual of a module sheaf with a
frame has a frame. -/
theorem IsFrame.dualFrame_isFrame {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    IsFrame (dualSheaf M) W hf.dualFrame := by
  intro W' h
  constructor
  · intro r r' hr
    have := congrArg (fun φ : Γ(dualSheaf M, W') => dualPair φ le_rfl (M.res h e)) hr
    simpa [dualPair_res_left] using this
  · intro φ
    exact ⟨_, hf.eq_smul_dualFrame h φ⟩

end AlgebraicGeometry.Scheme.Modules

end
