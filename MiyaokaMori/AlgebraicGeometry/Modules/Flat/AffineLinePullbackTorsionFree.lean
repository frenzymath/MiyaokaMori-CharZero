import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_Construction
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.KernelSections
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraLocallyWeightedPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.MonoOfAppInjectiveAffineCover
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsBaseChangeTransport

/-! # λ-torsion-freeness and flatness of `π : A¹_X → X` on module sheaves

Two local facts about the projection `π = toBase X : A¹_X = 𝔸(1; X) → X` and the coordinate `λ`, both stated for
quasi-coherent modules, and the λ-saturation of `π^*N ⊆ π^*M`:
* (L1) `mono_mulCoordPow_one_pullback_toBase`: multiplication by `λ` on `π^*N` is a monomorphism;
* (L2) `mono_pullback_toBase_map`: `π^*` preserves monomorphisms, i.e. `π` is flat on quasi-coherent modules.

Route (sections over the affine opens `π⁻¹U`, `U ⊆ X` affine): a morphism of quasi-coherent modules injective on sections
over an affine open cover is a monomorphism (`AffineLinePullbackTorsionFree_MonoOfAffineCover.lean`, via stalks =
localizations of sections, Stacks 01I8); on `π⁻¹U`, Stacks 01I9 identifies `Γ(π⁻¹U, π^*N) = Γ(π⁻¹U) ⊗_{Γ(U)} N(U)`
(`AffineLinePullbackTorsionFree_BaseChangeTransport.lean`), and `Γ(π⁻¹U) ≅ Γ(U)[λ]` (`exists_sections_preimage_equiv`,
`DeformedJetAlgebraLocallyWeightedPolynomial.lean`) is free over `Γ(U)` with `λ` having the left inverse `divX`.

From them (proved here): the **λ-saturation** of `π^*N` inside `π^*M` for a mono `i : N → M`
(`exists_pullback_toBase_map_app_eq_of_mulCoordPow`): a section `y` of `π^*M` with `λ^e·y ∈ π^*N` lies in `π^*N`.
This is the only local input of the exactness of the Rees syzygy sequence (`DeformedJetAlgebraSyzygy.lean`),
hence of the fibre at `λ = 0` (`DeformedJetAlgebraFiberAtZero.lean`).

Also here: generic section-level lemmas for morphisms of `O_X`-modules (`Hom.app_sum`, …, `app_injective_of_mono`).

References: Stacks 01I1 (`𝔸¹_U = Spec Γ(U)[t]`); Hartshorne III Prop. 9.2 (flatness of base changes of
`𝔸¹_ℤ → Spec ℤ`); the Rees deformation of §2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A morphism of `O_X`-modules is additive on sections: finite sums. -/
theorem Hom.app_sum {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) {ι : Type*} (s : Finset ι)
    (f : ι → Γ(M, U)) : φ.app U (∑ i ∈ s, f i) = ∑ i ∈ s, φ.app U (f i) :=
  map_sum (φ.app U).hom f s

theorem Hom.app_add' {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x y : Γ(M, U)) :
    φ.app U (x + y) = φ.app U x + φ.app U y :=
  map_add (φ.app U).hom x y

theorem Hom.app_neg' {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    φ.app U (-x) = -φ.app U x :=
  map_neg (φ.app U).hom x

theorem Hom.app_zero' {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    φ.app U (0 : Γ(M, U)) = 0 :=
  map_zero (φ.app U).hom

/-- `(φ - ψ)(x) = φ(x) - ψ(x)` on sections. -/
theorem Hom.sub_app_apply {M N : X.Modules} (φ ψ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    (φ - ψ).app U x = φ.app U x - ψ.app U x := rfl

/-- A monomorphism of `O_X`-modules is injective on sections over every open (`SheafOfModules.forget` is a right
adjoint, so it preserves monomorphisms; monomorphisms of presheaves of modules are objectwise injective,
`PresheafOfModules.injective_of_mono`). -/
theorem app_injective_of_mono {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) := by
  have : Mono φ.val :=
    @CategoryTheory.Functor.map_mono _ _ _ _ (SheafOfModules.forget _) inferInstance _ _ φ ‹_›
  intro a b hab
  exact PresheafOfModules.injective_of_mono φ.val (op U) hab

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.affineLineOver

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The affine opens `π⁻¹U`, `U ⊆ X` affine, cover `A¹_X` (`π⁻¹U ∋ y` iff `π y ∈ U`; affine opens cover `X`). -/
theorem exists_mem_preimage_toBase_affineOpens (y : affineLineOver X) :
    ∃ U : X.affineOpens, y ∈ toBase X ⁻¹ᵁ (U : X.Opens) := by
  obtain ⟨W, hW, hy, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X)
    (x := (toBase X).base y) (U := ⊤) trivial
  exact ⟨⟨W, hW⟩, hy⟩

/-- **`Γ(A¹_X, π⁻¹U) ≅ Γ(X, U)[λ]` as `Γ(X, U)`-algebras** for `U` affine, with `λ ↦ X` (the ring isomorphism
`exists_sections_preimage_equiv` is `Γ(X, U)`-linear because it sends
`π^♯ r` to the constant `C r`; the algebra structure on `Γ(A¹_X, π⁻¹U)` is the one through `π.appLE U (π⁻¹U)`, used by
the base-change transpose of Stacks 01I9). -/
theorem exists_algEquiv_sections_preimage {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    letI : Algebra Γ(X, U) Γ(affineLineOver X, toBase X ⁻¹ᵁ U) :=
      ((toBase X).appLE U (toBase X ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    ∃ e : Γ(affineLineOver X, toBase X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] MvPolynomial (ULift.{u} (Fin 1)) Γ(X, U),
      e (lambdaRes (toBase X ⁻¹ᵁ U)) = MvPolynomial.X default := by
  letI : Algebra Γ(X, U) Γ(affineLineOver X, toBase X ⁻¹ᵁ U) :=
    ((toBase X).appLE U (toBase X ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  obtain ⟨e, he, hC⟩ := exists_sections_preimage_equiv hU
  refine ⟨AlgEquiv.ofRingEquiv (f := e) fun a => ?_, ?_⟩
  · rw [MvPolynomial.algebraMap_eq]
    have h1 : algebraMap Γ(X, U) Γ(affineLineOver X, toBase X ⁻¹ᵁ U) a = ((toBase X).app U).hom a := by
      show ((toBase X).appLE U (toBase X ⁻¹ᵁ U) le_rfl).hom a = _
      rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
    rw [h1]
    exact hC a
  · show e (lambdaRes (toBase X ⁻¹ᵁ U)) = MvPolynomial.X default
    rw [he]
    rfl

/-- **(L1) `λ` is a nonzerodivisor on `π^*N`** for every quasi-coherent `N` on `X`: multiplication by the coordinate
`λ` (`mulCoordPow 1`) on the pullback `π^*N` along `π = toBase X : A¹_X → X` is a monomorphism.
Source: Stacks 01I1 (`𝔸¹_U = Spec Γ(U)[t]`), Stacks 01I8/01I9 (sections of quasi-coherent modules on affines and their
pullbacks); the Rees deformation of §2 of the paper lives inside `S[λ]`.

Proof (as formalized). A morphism of quasi-coherent modules that is injective on sections over an affine open cover is a
monomorphism (`Modules.mono_of_app_injective_of_isAffineOpen`: stalks
are localizations of the sections over an affine open, Stacks 01I8, and monomorphisms are detected on stalks). Take the
cover `π⁻¹U`, `U ⊆ X` affine (`π` is affine, `isAffineOpen_preimage_toBase`; `exists_mem_preimage_toBase_affineOpens`).
On `π⁻¹U`, `mulCoordPow 1` acts as `λ|_{π⁻¹U} •` (`mulCoordPow_app`), and by Stacks 01I9
(`Γ(π⁻¹U, π^*N) ≅ Γ(π⁻¹U) ⊗_{Γ(U)} N(U)`, `Γ(π⁻¹U)`-linearly; `Modules.smul_injective_of_smul_injective_tensor`) it
suffices that `λ •` is injective on `Γ(π⁻¹U) ⊗_{Γ(U)} N(U)`. Now `Γ(π⁻¹U) ≅ Γ(U)[X]` with `λ ↦ X` as `Γ(U)`-algebras
(`exists_algEquiv_sections_preimage`, from `exists_sections_preimage_equiv`), and `X` has the `Γ(U)`-linear left inverse
`divX` on `Γ(U)[X]` (`exists_linear_leftInverse_of_algEquiv_mvPolynomial`), so `λ • = (λ·) ⊗ 1` has the left inverse
`L ⊗ 1` and is injective (`smul_injective_of_leftInverse`).
Edge cases: `N = 0`, `X = ∅`: `π^*N = 0`, trivially mono. -/
theorem mono_mulCoordPow_one_pullback_toBase (N : X.Modules) [N.IsQuasicoherent] :
    Mono (mulCoordPow 1 ((Modules.pullback (toBase X)).obj N)) := by
  refine Modules.mono_of_app_injective_of_isAffineOpen _ (fun U : X.affineOpens => toBase X ⁻¹ᵁ (U : X.Opens))
    (fun U => isAffineOpen_preimage_toBase U.2) exists_mem_preimage_toBase_affineOpens fun U => ?_
  have hfun : ⇑((mulCoordPow 1 ((Modules.pullback (toBase X)).obj N)).app (toBase X ⁻¹ᵁ (U : X.Opens))) =
      fun x => lambdaRes (toBase X ⁻¹ᵁ (U : X.Opens)) • x := by
    funext x
    rw [mulCoordPow_app, pow_one]
  rw [hfun]
  refine Modules.smul_injective_of_smul_injective_tensor (toBase X) N U.1 (toBase X ⁻¹ᵁ (U : X.Opens)) le_rfl U.2
    (isAffineOpen_preimage_toBase U.2) (lambdaRes (toBase X ⁻¹ᵁ (U : X.Opens))) ?_
  letI : Algebra Γ(X, U.1) Γ(affineLineOver X, toBase X ⁻¹ᵁ U.1) :=
    ((toBase X).appLE U.1 (toBase X ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  obtain ⟨e, he⟩ := exists_algEquiv_sections_preimage (X := X) U.2
  obtain ⟨L, hL⟩ := MiyaokaMori.AffineLinePullbackTorsionFree.exists_linear_leftInverse_of_algEquiv_mvPolynomial e
    (lambdaRes (toBase X ⁻¹ᵁ U.1)) he
  exact MiyaokaMori.AffineLinePullbackTorsionFree.smul_injective_of_leftInverse _ L hL

/-- **(L2) `π^*` preserves monomorphisms** (`π : A¹_X → X` is flat): for quasi-coherent `N`, `M` and a monomorphism
`i : N → M`, `π^*i : π^*N → π^*M` is a monomorphism. Source: Hartshorne III Prop. 9.2 (flatness is stable under base
change and `𝔸¹_ℤ → Spec ℤ` is flat, `ℤ[t]` being free over `ℤ`); Stacks 01U2/02JY (flat morphisms); Stacks 01I1, 01I9.

Proof (as formalized). As in (L1), `Mono (π^*i)` is checked on sections over the affine opens `π⁻¹U`, `U ⊆ X` affine
(`Modules.mono_of_app_injective_of_isAffineOpen`). By Stacks 01I9 the base-change transpose identifies
`Γ(π⁻¹U, π^*N) ≅ Γ(π⁻¹U) ⊗_{Γ(U)} N(U)` naturally in the module (`Modules.pullback_map_app_injective_of_flat`), so `(π^*i).app (π⁻¹U) = 1 ⊗ i(U)`; `i(U)` is injective
(`Modules.app_injective_of_mono`) and `Γ(π⁻¹U) ≅ Γ(U)[X]` is a free, hence flat, `Γ(U)`-module
(`exists_algEquiv_sections_preimage`, `flat_of_algEquiv_mvPolynomial`), so `1 ⊗ i(U)` is injective
(`Module.Flat.lTensor_preserves_injective_linearMap`). Edge cases: `N = 0`, `X = ∅`: trivial. -/
theorem mono_pullback_toBase_map {N M : X.Modules} [N.IsQuasicoherent] [M.IsQuasicoherent] (i : N ⟶ M) [Mono i] :
    Mono ((Modules.pullback (toBase X)).map i) := by
  refine Modules.mono_of_app_injective_of_isAffineOpen _ (fun U : X.affineOpens => toBase X ⁻¹ᵁ (U : X.Opens))
    (fun U => isAffineOpen_preimage_toBase U.2) exists_mem_preimage_toBase_affineOpens fun U => ?_
  refine Modules.pullback_map_app_injective_of_flat (toBase X) M U.1 (toBase X ⁻¹ᵁ (U : X.Opens)) le_rfl U.2
    (isAffineOpen_preimage_toBase U.2) i ?_ (Modules.app_injective_of_mono i U.1)
  letI : Algebra Γ(X, U.1) Γ(affineLineOver X, toBase X ⁻¹ᵁ U.1) :=
    ((toBase X).appLE U.1 (toBase X ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  obtain ⟨e, -⟩ := exists_algEquiv_sections_preimage (X := X) U.2
  exact MiyaokaMori.AffineLinePullbackTorsionFree.flat_of_algEquiv_mvPolynomial e

/-- **λ-saturation of `π^*N ⊆ π^*M` on sections** (from (L1) and (L2)): if `λ·y` comes from `π^*N`, so does `y`.
Proof: let `q := π^*(coker.π i) : π^*M → π^*(coker i)`; `q(λy) = λ·q(y)` (`mulCoordPow_naturality`) and
`q(λy) = q(π^*i z) = 0`, so `q(y) = 0` by (L1) for `coker i` (quasi-coherent by Stacks 01IC, `isQuasicoherent_kernel`),
i.e. `y ∈ Γ(V, ker q)` (`exists_kernel_ι_app_eq`); `π^*` preserves cokernels (left adjoint), so `q` is a cokernel of the
monomorphism `π^*i` (L2), which is therefore the kernel of `q` (`Abelian.monoIsKernelOfCokernel`): `ker q → π^*M`
factors through `π^*i`. -/
theorem exists_pullback_toBase_map_app_eq_of_mulCoordPow_one {N M : X.Modules} [N.IsQuasicoherent]
    [M.IsQuasicoherent] (i : N ⟶ M) [Mono i]
    (V : (affineLineOver X).Opens) (y : Γ((Modules.pullback (toBase X)).obj M, V))
    (z : Γ((Modules.pullback (toBase X)).obj N, V))
    (h : ((Modules.pullback (toBase X)).map i).app V z =
      (mulCoordPow 1 ((Modules.pullback (toBase X)).obj M)).app V y) :
    ∃ z', ((Modules.pullback (toBase X)).map i).app V z' = y := by
  let P := Modules.pullback (toBase X)
  haveI : PreservesColimitsOfSize.{0, 0} P :=
    (Modules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits
  haveI := mono_pullback_toBase_map (X := X) i
  haveI : (cokernel i).IsQuasicoherent := (Modules.isQuasicoherent_kernel i).2
  let q : P.obj M ⟶ P.obj (cokernel i) := P.map (cokernel.π i)
  have hiq : P.map i ≫ q = 0 := by
    show P.map i ≫ P.map (cokernel.π i) = 0
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have hq : q.app V y = 0 := by
    haveI := mono_mulCoordPow_one_pullback_toBase (X := X) (cokernel i)
    apply Modules.app_injective_of_mono (mulCoordPow 1 (P.obj (cokernel i))) V
    have h1 := congrArg (fun φ : P.obj M ⟶ P.obj (cokernel i) => φ.app V y) (mulCoordPow_naturality 1 q)
    simp only [Modules.Hom.comp_app] at h1
    change q.app V ((mulCoordPow 1 (P.obj M)).app V y) =
      (mulCoordPow 1 (P.obj (cokernel i))).app V (q.app V y) at h1
    rw [← h1, ← h, map_zero]
    exact congrArg (fun φ : P.obj N ⟶ P.obj (cokernel i) => φ.app V z) hiq
  obtain ⟨w, hw⟩ := Modules.exists_kernel_ι_app_eq q V y hq
  have hcolim : IsColimit (CokernelCofork.ofπ q hiq) :=
    isColimitCoforkMapOfIsColimit' P (cokernel.condition i) (cokernelIsCokernel i)
  have hlim := Abelian.monoIsKernelOfCokernel (f := P.map i) _ hcolim
  let u : kernel q ⟶ P.obj N := hlim.lift (KernelFork.ofι (kernel.ι q) (kernel.condition q))
  have hu : u ≫ P.map i = kernel.ι q := hlim.fac _ WalkingParallelPair.zero
  refine ⟨u.app V w, ?_⟩
  have := congrArg (fun φ : kernel q ⟶ P.obj M => φ.app V w) hu
  simp only [Modules.Hom.comp_app] at this
  exact this.trans hw

/-- λ-saturation, iterated: `λ^e·y ∈ π^*N ⟹ y ∈ π^*N` (induction on `e`, `mulCoordPow_add`). -/
theorem exists_pullback_toBase_map_app_eq_of_mulCoordPow {N M : X.Modules} [N.IsQuasicoherent]
    [M.IsQuasicoherent] (i : N ⟶ M) [Mono i]
    (V : (affineLineOver X).Opens) (e : ℕ) (y : Γ((Modules.pullback (toBase X)).obj M, V))
    (z : Γ((Modules.pullback (toBase X)).obj N, V))
    (h : ((Modules.pullback (toBase X)).map i).app V z =
      (mulCoordPow e ((Modules.pullback (toBase X)).obj M)).app V y) :
    ∃ z', ((Modules.pullback (toBase X)).map i).app V z' = y := by
  induction e generalizing y with
  | zero =>
    refine ⟨z, h.trans ?_⟩
    rw [mulCoordPow_zero]
    rfl
  | succ e ih =>
    have hsplit : (mulCoordPow (e + 1) ((Modules.pullback (toBase X)).obj M)).app V y =
        (mulCoordPow e ((Modules.pullback (toBase X)).obj M)).app V
          ((mulCoordPow 1 ((Modules.pullback (toBase X)).obj M)).app V y) := by
      rw [Nat.add_comm, mulCoordPow_add]
      rfl
    rw [hsplit] at h
    obtain ⟨z'', hz''⟩ := ih _ h
    exact exists_pullback_toBase_map_app_eq_of_mulCoordPow_one i V y z'' hz''

end AlgebraicGeometry.Scheme.affineLineOver

end
