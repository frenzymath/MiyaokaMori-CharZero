import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.RingTheory.Localization.BaseChangeFiberDescent
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Local sections from ampleness on an open subscheme

**Ample on an open subscheme ⇒ a local section and an affine open**: let `L` be a line bundle on
`X`, `U ⊆ X` open, `L|_U` ample and `x ∈ U`. Then there are `n ≥ 1`, `s ∈ Γ(U, L^{⊗n})` (a section
of the sheaf `L^{⊗n}` on `X` over the open `U`) and an affine open `W ⊆ U` of `X` with `x ∈ W`, such
that for `y ∈ U`: `y ∈ W ⟺ s_y ∉ 𝔪_y (L^{⊗n})_y` (i.e. `W` is exactly the nonvanishing locus of
`s` inside `U`).

References: Stacks 0892, second paragraph of the proof ("`L|_{f^{-1}(Y_t)}` is ample, so we may
choose `n ≥ 1` and `s ∈ Γ(X_{f^*t}, L^{⊗n})` with `x ∈ (X_{f^*t})_s` affine") and the definition of
ampleness in Stacks 01PS; transport of sections, nonvanishing loci and affineness along open
immersions.

Proof sketch (matching the Lean proof step by step):
1. Let `ι : U → X` be the open immersion and `L' := ι^*L`. Ampleness of `L'` at the point
   `⟨x, hx⟩ : U` gives `n ≥ 1`, `σ ∈ Γ(U, L'^{⊗n})` with `⟨x,hx⟩ ∈ U_σ` and `U_σ` an affine open of `U`.
2. Pullback commutes with tensor powers: `θ := pullbackTensorPowIso ι L n : ι^*(L^{⊗n}) ≅ (ι^*L)^{⊗n}`.
   Put `σ' := θ⁻¹(σ)`; nonvanishing loci are invariant under isomorphisms (`nonvanishingLocus_iso`),
   so `U_{σ'} = U_σ`.
3. "Restriction ≅ pullback" for open immersions: `restrictFunctorIsoPullback ι`; the sections of
   `(restrictFunctor ι).obj F` over `⊤` are `Γ(F, ι ''ᵁ ⊤)` (`restrict_obj`, `rfl`), and `ι ''ᵁ ⊤ = U`.
   Put `s₀ := ρ⁻¹(σ') ∈ Γ(F, ι ''ᵁ ⊤)` (`F := L^{⊗n}`) and `s := s₀|_U`.
4. `W := ι ''ᵁ U_σ` is affine (`IsAffineOpen.image_of_isOpenImmersion`), `W ≤ U` (`ι_image_le`) and
   `x ∈ W` (`mem_ι_image_iff`).
5. Germs: for `y ∈ U` (`y' := ⟨y, hy⟩`), `y ∈ W ⟺ y' ∈ U_σ = U_{σ'} ⟺ σ'_{y'} ∉ 𝔪_{y'}`. Since
   `σ' = ρ(s₀)` and `ρ` on sections is "adjunction unit, then restriction"
   (`restrictFunctorIsoPullback_hom_app_apply`), `σ'_{y'} = u((s₀)_y) = u(s_y)` with
   `u : F_y → (ι^*F)_{y'}` the stalk map of the unit (`germ_restrictFunctorIsoPullback_hom_app`).
   Finally `u(s_y) ∈ 𝔪_{y'} ⟺ s_y ∈ 𝔪_y` (`modulePullbackStalkUnit_mem_maximalIdeal_smul_iff`: `⇐`
   from the local homomorphism, `map_nonunit`; `⇒` from `(ι^*F)_{y'} ≅ O_{U,y'} ⊗ F_y` and the
   base-change descent `BaseChangeFiberDescent.mem_maximalIdeal_smul_of_one_tmul`).

Edge cases: `U = ⊥`: `x ∈ U` is impossible, the conclusion is trivial; `X` empty: likewise; `n ≥ 1`
comes from ampleness.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-- The stalk map of the adjunction unit `u : M_{g x} → (g^*M)_x` preserves and reflects "lying in
the maximal ideal times the stalk": `u m ∈ 𝔪_x (g^*M)_x ⟺ m ∈ 𝔪_{g x} M_{g x}`. `⇐`: `u` is
semilinear over the local homomorphism `g^♯_x`, `map_nonunit`; `⇒`: `(g^*M)_x ≅ O_{X,x} ⊗ M_{g x}`
sends `u m` to `1 ⊗ m` (`modulePullbackStalkTensorInverse_unit`), then base-change descent
`mem_maximalIdeal_smul_of_one_tmul`. Holds for every module sheaf `M`. -/
theorem AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit_mem_maximalIdeal_smul_iff
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) (x : X)
    (m : M.presheaf.stalk (g.base x)) :
    AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x m ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x)) ↔
      m ∈ (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x))) •
          (⊤ : Submodule (Y.presheaf.stalk (g.base x)) (M.presheaf.stalk (g.base x))) := by
  let _ := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra g x
  constructor
  · intro h
    have hmem :=
      Submodule.mem_map_of_mem (f :=
        ((MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv g M x).symm :
          AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x →ₗ[X.presheaf.stalk x]
            AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensor g M x)) h
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at hmem
    have hinv :
        ((MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv g M x).symm :
            AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x →ₗ[X.presheaf.stalk x]
              AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensor g M x)
          (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x m) =
        (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (g.base x)] m :=
      MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorInverse_unit g M x m
    rw [hinv] at hmem
    exact MiyaokaMori.BaseChangeFiberDescent.mem_maximalIdeal_smul_of_one_tmul
      (g.stalkMap x).hom _ hmem
  · intro h
    have hle : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x))) •
          (⊤ : Submodule (Y.presheaf.stalk (g.base x)) (M.presheaf.stalk (g.base x))) ≤
        Submodule.comap (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x)
          ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x))) := by
      refine Submodule.smul_le.2 (fun r hr n _ => ?_)
      rw [Submodule.mem_comap, LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem_smul (map_nonunit _ r hr) Submodule.mem_top
    exact hle h

/-- The "restriction ≅ pullback" isomorphism of an open immersion `j` is, on sections, "adjunction
unit, then restriction" (`restrictFunctorIsoPullback_hom_app_apply`), so its germ is the stalk map of
the unit applied to the original germ (`modulePullbackStalkUnitAddHom_germ`). -/
theorem AlgebraicGeometry.Scheme.Modules.germ_restrictFunctorIsoPullback_hom_app
    {Z X : AlgebraicGeometry.Scheme.{u}} (j : Z ⟶ X) [AlgebraicGeometry.IsOpenImmersion j]
    (M : X.Modules) (W : Z.Opens) (t : Γ(M, j ''ᵁ W)) (z : Z) (hz : z ∈ W) :
    ((AlgebraicGeometry.Scheme.Modules.pullback j).obj M).presheaf.germ W z hz
        (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).app M).hom.app W t) =
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit j M z
        (M.presheaf.germ (j ''ᵁ W) (j.base z) (j.apply_mem_image_iff.mpr hz) t) := by
  rw [AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply,
    AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_apply,
    TopCat.Presheaf.germ_res_apply]
  exact (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ j M z (j ''ᵁ W) _ t).symm

/-- `L|_U` ample and `x ∈ U` ⇒ there are `n ≥ 1`, `s ∈ Γ(U, L^{⊗n})` and an affine open `W ⊆ U` with
`x ∈ W`, such that `W` is exactly the nonvanishing locus of `s` inside `U` (described pointwise by
germs). -/
theorem AlgebraicGeometry.IsAmple.exists_local_section_of_restrict {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (U : X.Opens)
    (hU : AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj L))
    (x : X) (hx : x ∈ U) :
    ∃ (n : ℕ) (_ : 0 < n) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, U)) (W : X.Opens),
      x ∈ W ∧ W ≤ U ∧ AlgebraicGeometry.IsAffineOpen W ∧
      ∀ (y : X) (hy : y ∈ U), y ∈ W ↔
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n).presheaf.germ U y hy s ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
            (⊤ : Submodule (X.presheaf.stalk y) ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).stalk y)) := by
  -- 1. the ampleness data
  obtain ⟨n, hn, σ, hxσ, haff⟩ := hU.2 ⟨x, hx⟩
  -- 2. σ' := θ⁻¹ σ ∈ Γ(U, ι^*(L^{⊗n}))
  let θ := AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso U.ι L n
  let σ' : Γ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n), ⊤) := θ.inv.app ⊤ σ
  have hσ' : ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n)).nonvanishingLocus σ' =
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj L) n).nonvanishingLocus σ :=
    AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso θ.symm σ
  -- 3. s₀ := ρ⁻¹ σ' ∈ Γ(F, ι ''ᵁ ⊤), s := s₀|_U
  let ρ := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app
    (AlgebraicGeometry.Scheme.Modules.tensorPow L n)
  let s₀ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, U.ι ''ᵁ ⊤) := ρ.inv.app ⊤ σ'
  have hs₀ : ρ.hom.app ⊤ s₀ = σ' :=
    AlgebraicGeometry.Scheme.Modules.modIso_hom_app_inv_app ρ ⊤ σ'
  have hle : U ≤ U.ι ''ᵁ ⊤ := le_of_eq U.ι_image_top.symm
  let s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, U) :=
    (AlgebraicGeometry.Scheme.Modules.tensorPow L n).presheaf.map (homOfLE hle).op s₀
  -- 4. W := ι ''ᵁ U_σ
  refine ⟨n, hn, s, U.ι ''ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow
    ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj L) n).nonvanishingLocus σ, ?_, ?_, ?_, ?_⟩
  · exact (AlgebraicGeometry.Scheme.Opens.mem_ι_image_iff U).mpr hxσ
  · exact U.ι_image_le _
  · exact haff.image_of_isOpenImmersion U.ι
  -- 5. the correspondence of germs
  intro y hy
  let y' : (U : AlgebraicGeometry.Scheme.{u}) := ⟨y, hy⟩
  have h1 : y ∈ U.ι ''ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj L) n).nonvanishingLocus σ ↔
      y' ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj L) n).nonvanishingLocus σ :=
    AlgebraicGeometry.Scheme.Opens.mem_ι_image_iff U (x := y')
  rw [h1, ← hσ']
  refine (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus _ σ' y').trans ?_
  have h2 := AlgebraicGeometry.Scheme.Modules.germ_restrictFunctorIsoPullback_hom_app U.ι
    (AlgebraicGeometry.Scheme.Modules.tensorPow L n) ⊤ s₀ y' trivial
  rw [hs₀] at h2
  have h3 : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).presheaf.germ (U.ι ''ᵁ ⊤) y (hle hy) s₀ =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n).presheaf.germ U y hy s :=
    (TopCat.Presheaf.germ_res_apply (AlgebraicGeometry.Scheme.Modules.tensorPow L n).presheaf
      (homOfLE hle) y hy s₀).symm
  have hgerm : ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow L n)).presheaf.germ ⊤ y' trivial σ' =
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit U.ι (AlgebraicGeometry.Scheme.Modules.tensorPow L n) y'
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).presheaf.germ U y hy s) := by
    rw [h2]
    exact congrArg _ h3
  rw [hgerm]
  exact not_congr (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit_mem_maximalIdeal_smul_iff
    U.ι (AlgebraicGeometry.Scheme.Modules.tensorPow L n) y' _)

end
