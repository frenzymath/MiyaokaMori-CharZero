import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroData
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousLocalFormula
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or

/-! # Factorization of the projectivization near the zero section

Statement: if the tuple of sections `P` is pointwise not all zero on the open `U` and satisfies all the vanishing
conditions of the homogeneous equations, then the projectivization of `P` factors through `X.embedding` as some
`Phi0 : U.toScheme ⟶ X.toScheme`, hence satisfies `IsTupleProjectivization`.

Proof: (1) build `projectivizationMorphism` from the pointwise nonvanishing; (2) use `hvanish` and
`projectivizationMorphism_factors` to obtain the factorization through the closed immersion; (3) package the
factorization equation as `IsTupleProjectivization`. Used in the proof of Theorem 4.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

theorem morphism_near_zero_projectivization_factorization_core {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {rho : FiniteCover k C}
    {L : LineBundle rho.source.toVariety}
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hvanish : ∀ j, evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (hU : ∀ v : U.toScheme, ∃ ℓ, ¬ IsZeroAt (sectionPullbackAlong U.ι (P ℓ)) v) :
    ∃ (Phi0 : U.toScheme ⟶ X.toScheme),
      IsTupleProjectivization
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules)
        P U Phi0 := by
  -- Step 2 (hypothesis of `projectivizationMorphism_factors`): the equations still vanish on `U`.
  have hzero : ∀ j, evalHomogeneousAtSections
      ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules))
      (D.E.F j) (D.E.homogeneous j) (fun ℓ ↦ sectionPullbackAlong U.ι (P ℓ)) = 0 := by
    intro j
    -- `U.ι` is a `k`-morphism: the `k`-structure of `U` is by definition `U.ι ≫ (Tot L ↘ Spec k)`.
    have : U.ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
    rw [← evalHomogeneousAtSections_pullback (k := k) U.ι _ (D.E.F j) (D.E.homogeneous j) P,
      hvanish j, sectionPullbackAlong_zero]
    exact map_zero _
  -- Steps 1–2: factor the glued projectivization `U → P^N` through the closed immersion `X ↪ P^N`.
  obtain ⟨Phi0, hPhi0⟩ := projectivizationMorphism_factors (k := k) X.embedding D.E.deg D.E.F
    D.E.homogeneous D.E.spans _ (fun ℓ ↦ sectionPullbackAlong U.ι (P ℓ)) hU hzero
  -- Step 3: package as `IsTupleProjectivization`.
  exact ⟨Phi0, hU, hPhi0⟩

end
