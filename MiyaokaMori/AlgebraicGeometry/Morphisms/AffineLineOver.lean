import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.SectionClosedImmersion

/-! # The affine line over a scheme

The affine line `A¹_X = 𝔸(Fin 1; X)` over a scheme `X`, with the projection `toBase : A¹_X → X`,
the map `toLine : A¹_X → A¹_k` (when `X` is a `k`-scheme), the section `sectionAt t : X → A¹_X`
at `λ = t`, the `k`-rational point `point k t` of `A¹_k`, and the evaluation
`evalAt t W : Γ(A¹_X, toBase⁻¹W) → Γ(X, W)` at `λ = t`.

This is the base of the deformation family over `C × A¹` used in Lemma 2.3 of
the paper (reduction to a split weighted bundle).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.Scheme.affineLineOver (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X

noncomputable def AlgebraicGeometry.Scheme.affineLineOver.toBase (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.affineLineOver X ⟶ X :=
  AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) X ↘ X

noncomputable def AlgebraicGeometry.Scheme.affineLineOver.toLine {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    AlgebraicGeometry.Scheme.affineLineOver X ⟶
      AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  AlgebraicGeometry.AffineSpace.map (n := ULift.{u} (Fin 1))
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- The section at `λ = t`: the coordinate is the constant `t`. -/

noncomputable def AlgebraicGeometry.Scheme.affineLineOver.sectionAt {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (t : k) :
    X ⟶ AlgebraicGeometry.Scheme.affineLineOver X :=
  AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id X)
    (fun _ => (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t))

/-- The closed point `λ = t` of `A¹_k`. -/

noncomputable def AlgebraicGeometry.Scheme.affineLineOver.point (k : Type u) [Field k] (t : k) :
    AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  letI : (AlgebraicGeometry.Spec (CommRingCat.of k)).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.CategoryStruct.id _⟩
  (AlgebraicGeometry.Scheme.affineLineOver.sectionAt (k := k) (AlgebraicGeometry.Spec (CommRingCat.of k)) t).base
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)

open AlgebraicGeometry in

/-- Evaluation at `λ = t`: the map `Γ(A¹_X, toBase⁻¹ W) = Γ(X, W)[λ] → Γ(X, W)`, i.e. pullback
along `sectionAt t`. -/

noncomputable def AlgebraicGeometry.Scheme.affineLineOver.evalAt {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (t : k)
    (W : X.Opens) :
    Γ(AlgebraicGeometry.Scheme.affineLineOver X, AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W) ⟶
      Γ(X, W) :=
  (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).appLE
    (AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W) W (by
      -- `sectionAt t ≫ toBase = 𝟙` (`AffineSpace.homOfVector_over`), hence `W ≤ sectionAt⁻¹(toBase⁻¹ W)`
      have e : AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase X = CategoryTheory.CategoryStruct.id X :=
        AlgebraicGeometry.AffineSpace.homOfVector_over _ _
      intro x hx
      have hx' : (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase X).base x ∈ W := by rw [e]; exact hx
      simpa using hx')

end
