import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAssemblyUniqueAxioms

/-! # Assembly, part 3c: uniqueness of twist families over an open of a piece

Two relative twist families on an open `V` of a piece give two absolute twist section families on `V`
(`isSectionFamily_toSectionFamily`, part 3b), which coincide by `Proj.TwistFamily.IsSectionFamily.eq` (AU); reading the
equality at `⊤` gives `twistFamily_sectionMap_unique'`, i.e. (U) with the `Aux` predicate.
See `RelativeProjLiftEvaluationTwistFamily.lean`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T : AlgebraicGeometry.Scheme.{u}}

namespace LiftData

variable {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules} [M.IsLineBundle]
  (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)

attribute [local instance] AlgebraicGeometry.Scheme.relativeProj.isIso_powTriv



/-- **(U′) Uniqueness of twist families over a piece, stated with the `Aux` predicate** (the locked statement
`twistFamily_sectionMap_unique` in `RelativeProjLiftEvaluationTwistFamily.lean` is this one up to `rfl`). Original docstring:
**(U) Uniqueness of twist families over a piece** (Stacks 01O4: the pair `(L, ψ)` determines the morphism and
the isomorphism `r^*O(n) ≅ L^{⊗n}` "up to strict equivalence"; 01MN for the generators). Over an open `V` of a piece
`V'` (chart `W`, trivialization `e`), any two twist families `ψ¹` (on `V₁ ⊇ V`) and `ψ²` (on `V₂ ⊇ V`) have the same
section maps `Γ(τ^*O(n), V) → Γ(M^{⊗n}, V)` in every degree `n`.

**Natural-language proof (complete, as things stand; single chart `W`, no chart change).** Notation as in
`exists_twistFamily_of_piece`: `A = S.sectionsRing W`, `𝒜`, `Φ`, `φ = fromOfGlobalSections 𝒜 Φ _`,
`liftLocal = φ ≫ affineIso.inv ≫ (π⁻¹W).ι = V'.ι ≫ τ` (`hτ`).
1. *Localize.* Both section maps are additive and natural in the open (`sectionMapOfRestrictHom_nat`) and
   `O`-linear (`sectionMapOfRestrictHom_smul`); by the sheaf property it suffices to compare them after restriction to
   each member of the open cover of `V` by `V_s := V ⊓ V'.basicOpen (Φ s)`, `s ∈ 𝒜_d`, `d > 0` (these cover `V'`
   because `Φ` maps the irrelevant ideal onto `⊤`: Mathlib `openCoverOfMapIrrelevantEqTop`), and there on a set of
   local generators.
2. *Generators (01MN).* `V'.basicOpen (Φ s) = liftLocal⁻¹(D₊(s))` (`fromOfGlobalSections_preimage_basicOpen`,
   transported by `affineIso`), and `O(n)|_{π⁻¹W}` is the pullback under `affineIso` of `Proj.twist 𝒜 n`
   (`twistAffineIso`, 01NR), whose sections over `D₊(s)` are exactly the fractions `a/s^k`, `a ∈ 𝒜_{n+kd}`
   (`Stacks01n2TwistStalkSections`). A pullback `f^*F` is generated, locally, by the pullbacks of local sections of
   `F` (`modulePullbackStalkTensorMap_bijective`), so over `B ≤ V_s` the module `τ^*O(n)` is locally generated
   by the sections `σ_{a,k} := τ^*(a/s^k)`; two additive, `O`-linear, natural maps agreeing on these agree.
3. *Key identity.* In `Γ(τ^*O(n+kd), V_s)`: `μ(σ_{a,k} ⊗ τ^*(s/1)^{⊗k}) = τ^*(a/1)` — the fraction identity
   `(a/s^k)·(s/1)^k = a/1` (`Proj.twistSectionMul`), transported: `twistMulHom` restricted to `π⁻¹W` is
   `twistMulLocal S a b W`, the transport of `Proj.twistMul 𝒜` (`twistMul` is `glueHom` of `twistMulLocal`,
   `Modules.glueHom_app`). Here `τ^*(s/1)|_{V'} = α_d(η s)` and `τ^*(a/1)|_{V'} = α_{n+kd}(η a)` by
   `evaluationPresheafHom_app_affine` and `evaluationLocal_eq` (`x/1 = Proj.twistSection (sectionsOf x)`).
   For a twist family `ψ`: (M) iterated gives `ψ_{n+kd}(σ · (s/1)^k) = monoidalPowCat(ψ_n(σ) ⊗ ψ_d(s/1)^{⊗k})`, and
   (F) gives `ψ_d(s/1) = β_d(η s) = Ψ_d(η s) =: Ψ(s)` and `ψ_{n+kd}(a/1) = Ψ(a)`. Hence, for both families,
   `ψ_n(σ_{a,k}) ⊗ Ψ(s)^{⊗k} = Ψ(a)` in `Γ(M^{⊗(n+kd)}, V_s)` (through `monoidalPowCat`).
4. *Cancel the frame.* On `V_s`, `Ψ(s)` is a nowhere-vanishing section of the line bundle `M^{⊗d}`: through the
   trivialization `e` (restricted to `V'`), `e^{⊗d}(Ψ(s)) = Φ(s)` restricted to `V'.basicOpen (Φ s)`
   (`liftLocalPiece_apply`, definition of `liftLocalHom`), a unit (`RingedSpace.isUnit_res_basicOpen`). Tensoring
   with a nowhere-vanishing section of a line bundle is injective on sections (on a trivializing open it is
   multiplication by a unit; `M^{⊗kd}` is a line bundle, `Modules.monoidalPow_isLineBundle'`). Therefore
   `ψ¹_n(σ_{a,k}) = ψ²_n(σ_{a,k})`, and by 1–2 the section maps agree on `V`. ∎


**Edge cases.** `V = ∅`: trivial. `k = 0`: step 3 is (F) itself. `n = 0`: `σ = a/s^k` with `a ∈ 𝒜_{kd}`. The
hypothesis `hτ` comes from `exists_lift_restrict`; the two families may live on different opens
`V₁, V₂ ⊇ V` (this is how it is used on overlaps of pieces). -/
theorem twistFamily_sectionMap_unique'
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hτ : V'.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V' hV' hle)
    (V : T.Opens) (hV : V ≤ V') {V₁ V₂ : T.Opens}
    (ψ₁ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (ψ₂ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₂.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₂.ι)
    (h₁ : V ≤ V₁) (h₂ : V ≤ V₂)
    (H₁ : D.IsTwistFamilyOnAux V₁ ψ₁ V h₁) (H₂ : D.IsTwistFamilyOnAux V₂ ψ₂ V h₂) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ₁ n) V h₁ =
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ₂ n) V h₂ := by
      classical
  -- `V` as a generalized piece
  have hleV : V ≤ U ⊓ f ⁻¹ᵁ W.1 := hV.trans hle
  have hΦ' := AlgebraicGeometry.Scheme.relativeProj.pieceRingHom_map_irrelevant S f M D U e W hle hV'
  have heq : AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hleV =
      (T.homOfLE hV).appTop.hom.comp (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) := by
    rw [AlgebraicGeometry.Scheme.relativeProj.pieceRingHom_eq, AlgebraicGeometry.Scheme.relativeProj.pieceRingHom_eq,
      ← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← AlgebraicGeometry.Scheme.Hom.comp_appTop,
      AlgebraicGeometry.Scheme.homOfLE_homOfLE]
  have hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hleV) = ⊤ := by
    rw [heq]
    exact AlgebraicGeometry.Proj.ProjectiveTupleRestriction.irrelevant_map_eq_top_comp _ _ _ hΦ'
  have hτV := AlgebraicGeometry.Scheme.relativeProj.ι_lift_eq_pieceMap_comp_of_le S f M D U e W V' hV' hle hτ hV hΦ
  -- the two absolute section families coincide (Stacks 01O4, uniqueness)
  have hc := AlgebraicGeometry.Proj.TwistFamily.IsSectionFamily.eq (S.sectionsGrading W.1)
    (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hleV) hΦ
    (D.isSectionFamily_toSectionFamily U e W hleV hΦ hτV ψ₁ h₁ H₁)
    (D.isSectionFamily_toSectionFamily U e W hleV hΦ hτV ψ₂ h₂ H₂)
  -- read the equality at `B' = ⊤`
  have hΛ := AlgebraicGeometry.Scheme.relativeProj.isIso_powTriv f M U e W hleV n
  have hTop : V.ι ''ᵁ (⊤ : V.toScheme.Opens) ≤ V := AlgebraicGeometry.Scheme.relativeProj.LiftData.image_le_self ⊤
  have hTop' : V ≤ V.ι ''ᵁ (⊤ : V.toScheme.Opens) := by rw [AlgebraicGeometry.Scheme.Opens.ι_image_top]
  have key : ∀ x₀ : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)), V.ι ''ᵁ (⊤ : V.toScheme.Opens)),
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ₁ n) (V.ι ''ᵁ ⊤) (hTop.trans h₁) x₀ =
        AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ₂ n) (V.ι ''ᵁ ⊤) (hTop.trans h₂) x₀ := by
    intro x₀
    have h := congrFun (congrFun (congrFun hc n) ⊤) ((D.twistTransport U e W hleV hΦ hτV n).hom.app ⊤ x₀)
    unfold AlgebraicGeometry.Scheme.relativeProj.LiftData.toSectionFamily at h
    rw [AlgebraicGeometry.Scheme.Modules.iso_inv_app_hom_app_tfa (D.twistTransport U e W hleV hΦ hτV n) ⊤ x₀] at h
    exact (ConcreteCategory.bijective_of_isIso
      ((AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hleV n).app ⊤)).1 h
  ext x
  have n1 := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_nat (ψ₁ n) V (V.ι ''ᵁ ⊤) h₁ hTop) x
  have n2 := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_nat (ψ₂ n) V (V.ι ''ᵁ ⊤) h₂ hTop) x
  simp only [ConcreteCategory.comp_apply] at n1 n2
  apply AlgebraicGeometry.Scheme.Modules.presheaf_map_injective_of_le_le
    (AlgebraicGeometry.Scheme.Modules.monoidalPow M n) hTop hTop'
  rw [← n1, ← n2]
  exact key _

end LiftData

end AlgebraicGeometry.Scheme.relativeProj

end
