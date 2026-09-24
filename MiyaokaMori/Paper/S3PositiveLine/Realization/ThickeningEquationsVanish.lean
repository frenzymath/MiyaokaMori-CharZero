import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Realization.EquationsVanishIdentically
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalarOfCoefficientsZero
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.ThickeningEquationsVanishGeneral

/-! # The truncated cone equations vanish

The truncation to the `κ`-th infinitesimal neighbourhood `C̃_(κ)(L)` of the evaluated cone equation
`F_j(P_0, …, P_N)` vanishes, when the tuple `P` restricts to the cone coordinates of a based jet.
This is the input `hjet` of `equations_vanish_identically` in the proof of Theorem 4.2 of the paper.

Source: proof of Theorem 4.2 of the paper ("in a local frame of `L`, its reduction modulo `t^{k+1}`
is zero, because `ȷ` takes values in `𝒵`").

Proved from the variable-level lemmas of `ThickeningEquationsVanishGeneral` and the bridge
`restrictToThickening_eq_thickeningRestrict` (see its docstring in `GenericallyScalarOfCoefficientsZero`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The canonical identification `(p_L^*M)^{⊗e} ≅ p_L^*(M^{⊗e})` on `Tot(L)`: the inverse of the
pullback–tensor-power comparison `pullbackTensorPowIso`,
followed by the pullback of `moduleTensorPowerIsoTensorPow` identifying `LineBundle.zpow M e`
(whose underlying module is `AlgebraicGeometry.Scheme.Modules.moduleTensorPower M.toModules e`) with `tensorPow M.toModules e`.
This is the `θ` fed to `equations_vanish_identically`. -/
noncomputable def totalSpaceZpowIso {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (e : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) e ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.zpow e).toModules :=
  (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules e).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).mapIso
        (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerIsoTensorPow M.toModules e).symm

/-- **The cone equations vanish on the cone coordinates of a based jet**: for the `k`-structure
`p_κ ≫ (C̃ ↘ Spec k)` on `C̃_(κ)(L)`, `F_j(P_0^{(κ)}, …, P_N^{(κ)}) = 0` in
`Γ(C̃_(κ)(L), (p_κ^* A_ρ)^{⊗ d_j})`, where `P_ℓ^{(κ)} = BasedJet.coneCoordinate jet ℓ`.

Source: Theorem 4.2 of the paper ("because ȷ takes values in 𝒵").

Proof. By definition the cone coordinates are
`P_ℓ^{(κ)} = Φ₁(Φ₂(z_ℓ))`, where `z_ℓ = (q^*π_ℓ)(σ)` is the `ℓ`-th coordinate of the section
`σ ∈ Γ(C̃_(κ)(L), q^* A^{⊕(N+1)})` corresponding under `totalSpaceHomEquiv` to
`jet.hom ≫ coneι : C̃_(κ)(L) → 𝒵 ↪ Tot(A^{⊕(N+1)})` (`q = p_κ ≫ ρ`, `A = seedLineBundle X.embedding f`),
`Φ₂ = (pullbackComp p_κ ρ)⁻¹ : q^*A → p_κ^*ρ^*A` and `Φ₁ = p_κ^*ρ^*f^*(eqToHom (OX_toModules 1)⁻¹)`.
Naturality of the homogeneous evaluation under module maps (`evalHomogeneousAtSections_map`) gives `F_j(Φ₁ ∘ Φ₂ ∘ z) = Φ₁^{⊗d}(Φ₂^{⊗d}(F_j(z)))`, and `F_j(z) = 0` is
`evalHomogeneousAtSections_coordinates_eq_zero_of_factors_cone` (the equations vanish on the
coordinates of any morphism into the cone, Stacks 02OR), applied to `j₀ = jet.hom`, `q = p_κ ≫ ρ`,
`hq = jet.over`, and the structure morphism identity `p_κ ≫ (C̃ ↘ Spec k) = (p_κ ≫ ρ) ≫ (C ↘ Spec k)`
(`ρ.isOver`). -/
theorem BasedJet.evalHomogeneousAtSections_coneCoordinate_eq_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (jet : BasedJet f ρ L κ) (j : D.E.ι) :
    letI : (jetNeighborhood L κ).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨jetNeighborhood.proj L κ ≫ (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    evalHomogeneousAtSections
      ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
        (seedBundlePullback f ρ).toModules) (D.E.F j) (D.E.homogeneous j)
      (fun ℓ => BasedJet.coneCoordinate jet ℓ) = 0 := by
  let _ : (jetNeighborhood L κ).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨jetNeighborhood.proj L κ ≫ (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let A := seedLineBundle X.embedding f
  let V := AlgebraicGeometry.Scheme.Modules.pow A (X.embDim + 1)
  let p := jetNeighborhood.proj L κ
  let coneι : (MMSetup.cone f).left ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left :=
    (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A X.embDim (D.E.F j) (D.E.homogeneous j))).subschemeι
  have hq : (jet.hom ≫ coneι) ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = p ≫ ρ.hom := by
    rw [Category.assoc]
    exact jet.over
  let toTot : CategoryTheory.Over.mk (p ≫ ρ.hom) ⟶ AlgebraicGeometry.Scheme.totalSpace V :=
    CategoryTheory.Over.homMk (jet.hom ≫ coneι) hq
  let z : Fin (X.embDim + 1) →
      ((((AlgebraicGeometry.Scheme.Modules.pullback (p ≫ ρ.hom)).obj A).val.obj (Opposite.op ⊤)) : Type u) :=
    fun ℓ => (((AlgebraicGeometry.Scheme.Modules.pullback (p ≫ ρ.hom)).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (X.embDim + 1) => A) ℓ)).val.app
        (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (p ≫ ρ.hom)) toTot)
  let Φ₂ : (AlgebraicGeometry.Scheme.Modules.pullback (p ≫ ρ.hom)).obj A ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback p).obj ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj A) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ.hom).inv.app A
  let Φ₁ : (AlgebraicGeometry.Scheme.Modules.pullback p).obj ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj A) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback p).obj (seedBundlePullback f ρ).toModules :=
    (AlgebraicGeometry.Scheme.Modules.pullback p).map
      ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).map
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1).symm)))
  have hcone : (fun ℓ => BasedJet.coneCoordinate jet ℓ) =
      fun ℓ => (Φ₁.val.app (Opposite.op ⊤)).hom ((Φ₂.val.app (Opposite.op ⊤)).hom (z ℓ)) := by
    funext ℓ
    rfl
  rw [hcone, evalHomogeneousAtSections_map Φ₁ (D.E.F j) (D.E.homogeneous j),
    evalHomogeneousAtSections_map Φ₂ (D.E.F j) (D.E.homogeneous j)]
  have hz : evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback (p ≫ ρ.hom)).obj A)
      (D.E.F j) (D.E.homogeneous j) z = 0 := by
    refine evalHomogeneousAtSections_coordinates_eq_zero_of_factors_cone A X.embDim D.E.deg D.E.F
      D.E.homogeneous jet.hom (p ≫ ρ.hom) hq ?_ j
    show p ≫ (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (p ≫ ρ.hom) ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [Category.assoc, ρ.isOver]
  rw [hz, map_zero, map_zero]

/-- **Truncated cone equations vanish.**

Source: proof of Theorem 4.2 of the paper.

* Paper: `F_j(P_0,…,P_N)`, a section of `π_L^*ρ^*A^{⊗d_j}`, has zero reduction modulo `t^{k+1}` because `ȷ` takes
  values in `𝒵`. Here `(seedBundlePullback f ρ).zpow d_j` is the Lean carrier of `A_ρ^{⊗d_j}`,
  `restrictToThickening … κ` is the reduction to `C̃_(κ)(L)`, and `hjet` is the paper's "their restrictions to
  `C̃_(k)(L)` recover the coordinates of `ȷ`".
* The transport iso is immaterial: the general lemma `thickeningRestrict_map_evalHomogeneous_eq_zero`
  behind the proof holds for an *arbitrary* morphism `Θ`, so the same statement is provable verbatim for any
  other identification `(p_L^*A_ρ)^{⊗d} ≅ p_L^*(A_ρ^{⊗d})`; and the only user, `realization_hvanish` in
  `RealizationGeometricBack`, feeds this theorem as `hjet` to
  `equations_vanish_identically` with `θ := totalSpaceZpowIso`, whose conclusion `F_j(P) = 0` does not
  mention `θ` at all.
* Not vacuous: downstream, `jet` is the based jet from `positive_line`, `P` the coefficient-section tuple of
  `realization_hzero`, and `hjet` is `realization_hjet`.
  `realization_hzero`, and `hjet` is `realization_hjet`.

Setting: `A_ρ = ρ^*f^*O_X(1)` (`seedBundlePullback f ρ`), `P_ℓ ∈ Γ(Tot(L), p_L^*A_ρ)` a tuple whose truncation to
the `κ`-th neighbourhood `C̃_(κ)(L) ⊂ Tot(L)` (`jetNeighborhood L κ`, closed immersion
`jetNeighborhood.toTotalSpace L κ`) is the `ℓ`-th cone coordinate of the based jet `jet`
(`hjet`), `F_j` the homogeneous defining equations of the cone `𝒵 = MMSetup.cone f` (degree `d_j = D.E.deg j`).

Proof.
1. `restrictToThickening L M κ` is `thickeningRestrict i p_L h M` for the closed immersion
   `i = (jetNeighborhood.toTotalSpace L κ).left`, `h : i ≫ p_L = p_κ` (`toTotalSpace_proj`); this is the
   bridge `restrictToThickening_eq_thickeningRestrict`.
   Rewrite the goal and `hjet` with it.
2. Put the `k`-structure `p_κ ≫ (C̃ ↘ Spec k)` on `C̃_(κ)(L)`; `i` is then a `k`-morphism, since
   `Tot(L) ↘ Spec k = p_L ≫ (C̃ ↘ Spec k)` (`totalSpace.canonicallyOver`) and `i ≫ p_L = p_κ`.
3. `thickeningRestrict_map_evalHomogeneous_eq_zero` (variable-level, `ThickeningEquationsVanishGeneral`):
   the restriction of `Θ(F_j(P))` vanishes as soon as `F_j` of the restricted tuple vanishes. By `hjet` the
   restricted tuple is `(coneCoordinate jet ℓ)_ℓ`, and `F_j(coneCoordinate jet) = 0` is
   `BasedJet.evalHomogeneousAtSections_coneCoordinate_eq_zero` (the jet takes values in the cone `𝒵`).
Edge cases: `κ = 0` (the neighbourhood is `C̃` itself) and no equations (`D.E.ι` empty) need no separate
treatment. Instead of `homogeneousEquationSection_le_ker_totalSpaceSection_iff`, the Stacks 02OR
direction "factors through the zero scheme ⇒ pulled-back section vanishes"
(`sectionPullbackAlong_subschemeι_eq_zero`) is used. -/
theorem restrictToThickening_evalHomogeneous_eq_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (jet : BasedJet f ρ L κ)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj (Opposite.op ⊤) : Type u))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ
        = restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ)) (j : D.E.ι) :
    restrictToThickening L ((seedBundlePullback f ρ).zpow (D.E.deg j)) κ
      ((totalSpaceZpowIso L (seedBundlePullback f ρ) (D.E.deg j)).hom.app ⊤
        (evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P)) = 0 := by
  let _ : (jetNeighborhood L κ).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨jetNeighborhood.proj L κ ≫ (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have _ : (jetNeighborhood.toTotalSpace L κ).left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    show (jetNeighborhood.toTotalSpace L κ).left ≫
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫
          (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      jetNeighborhood.proj L κ ≫ (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [← Category.assoc, jetNeighborhood.toTotalSpace_proj]⟩
  refine (restrictToThickening_eq_thickeningRestrict L _ κ _).trans ?_
  refine thickeningRestrict_map_evalHomogeneous_eq_zero (k := k) (jetNeighborhood.toTotalSpace L κ).left
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (jetNeighborhood.toTotalSpace_proj L κ)
    (seedBundlePullback f ρ).toModules (D.E.F j) (D.E.homogeneous j) P ?_ _
  have hjet' : (fun ℓ => thickeningRestrict (jetNeighborhood.toTotalSpace L κ).left
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (jetNeighborhood.toTotalSpace_proj L κ)
      (seedBundlePullback f ρ).toModules (P ℓ)) = fun ℓ => BasedJet.coneCoordinate jet ℓ := by
    funext ℓ
    exact ((hjet ℓ).trans (restrictToThickening_eq_thickeningRestrict L _ κ (P ℓ))).symm
  rw [hjet']
  exact BasedJet.evalHomogeneousAtSections_coneCoordinate_eq_zero jet j

end
