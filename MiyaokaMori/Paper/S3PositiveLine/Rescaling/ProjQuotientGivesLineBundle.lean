import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleEpiIso
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation

/-! # A degree-one presentation of the relative Proj gives a line bundle

A surjection `ρ^*S_m ↠ L^{-m}` gives `τ` together with an isomorphism `τ^*O(m) ≅ L^{-m}`
(§3 of the paper: "the degree-one presentation of the Veronese Proj").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree-one presentation of the relative Proj (§3 of the paper). Let `τ : ρ.source → Y_k^GG = Proj_C S`
be over `C` (`hτ`), let `φ : (τ ≫ π_k)^*S_m ↠ L^{-m}` be an epimorphism induced by `τ` (`relativeProj.InducedBy`:
`φ` factors through `τ^*(evaluation π^*S_m → O(m))` as `… ≫ ψ` with `ψ : τ^*O(m) → L^{-m}`). Then `τ^*O(m) ≅ L^{-m}`.

Proof: `InducedBy` gives `ψ` and `φ = (pullback-composition iso)⁻¹ ≫ τ^*(evaluation) ≫ ψ`. Since `φ` is an
epimorphism and `g ≫ ψ` epi implies `ψ` epi (`CategoryTheory.epi_of_epi`, twice), `ψ` is an epimorphism.
`O(m) = polarization f κ m` is a line bundle for `m` sufficiently divisible (`polarization_isLineBundle`, from
`relativeProj.isLineBundle_twist`), pullbacks of line bundles are line bundles (`IsLineBundle.pullback`), and
`L^{-m}` is the underlying module sheaf of a packaged line bundle (`LineBundle.toModules_isLineBundle`).
An epimorphism between line bundles is an isomorphism (`SheafOfModules.IsLineBundle.isIso_of_epi`), so `ψ` is an
isomorphism and `asIso ψ` is the required one. Representability of Proj is not used; `hτ` is not used by the proof
either (that `τ` lies over `C` is already implied by the type of `InducedBy`) but is kept in the statement. -/
theorem pullback_polarization_of_surjection {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)] (ρ : FiniteCover k C)
    (L : LineBundle ρ.source.toVariety)
    (τ : ρ.source.toScheme ⟶ YGG f κ) (hτ : τ ≫ YGG.proj f κ = ρ.hom)
    (φ : (AlgebraicGeometry.Scheme.Modules.pullback (τ ≫ YGG.proj f κ)).obj ((jetAlgebra f κ).part m)
      ⟶ (L.zpow (-(m : ℤ))).toModules)
    (hsurj : CategoryTheory.Epi φ)
    (hcompat : AlgebraicGeometry.Scheme.relativeProj.InducedBy τ φ) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj (polarization f κ m)
      ≅ (L.zpow (-(m : ℤ))).toModules) := by
  obtain ⟨ψ, hψ⟩ := hcompat
  -- φ = (iso) ≫ τ^*(evaluation) ≫ ψ is epi, hence ψ is epi
  have hepi : CategoryTheory.Epi ψ := by
    rw [hψ] at hsurj
    exact @CategoryTheory.epi_of_epi _ _ _ _ _ _ ψ (@CategoryTheory.epi_of_epi _ _ _ _ _ _ _ hsurj)
  -- both source and target of ψ are line bundles: O(m) = polarization f κ m is a line bundle when
  -- m is sufficiently divisible (polarization_isLineBundle), pullbacks of line bundles are line
  -- bundles (IsLineBundle.pullback), and L^{-m} is a packaged line bundle
  -- (LineBundle.toModules_isLineBundle). The instances are passed explicitly because the type of
  -- ψ shows `polarization f κ m` unfolded, which instance search does not see through.
  have hM : ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj (polarization f κ m)).IsLineBundle :=
    inferInstance
  have hN : (L.zpow (-(m : ℤ))).toModules.IsLineBundle := inferInstance
  have hiso : CategoryTheory.IsIso ψ :=
    @SheafOfModules.IsLineBundle.isIso_of_epi _ _ _ hM hN ψ hepi
  exact ⟨@CategoryTheory.asIso _ _ _ _ ψ hiso⟩

end
