import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundleDualIsoPullbackOmega
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetLinearPiece_Defs
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetLinearPiece_FreeRank
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetLinearPiece_Naturality
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetAlgebraLocallyWeightedPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.IsIsoOfAffineOpensCoverBijective
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # The linear piece of the jet algebra is `E^∨`, under the smoothness hypotheses of the paper

For `S := (jetGradedAlgebra Z sec hs r).1` the jet graded algebra and `E := coneTangentBundle Z.hom sec hs = sec^*T_{Z/C}`,
the weight-`(q+1)` linear piece `S_{q+1}/I^{(2)}_{q+1}` (`cokernel (S.irrelevantPow 2 (q+1)).2`) is isomorphic to
`E^∨ = Modules.dual E`.

## Why the smoothness hypotheses are needed

A version assuming only `hloc` (`S` is locally a weighted polynomial algebra in `(n+1)r` variables), `hE : E.rank = n+1`
and `hEZ : E ≅ sec^*T_{Z/C}` **is false**:
* Take `C = ℙ¹`, `L₁ = O(1)`, `L₂ = O`, and `Z := Spec_C (Sym(L₁^∨) ×_{O_C} Sym(L₂^∨))` — the two total spaces
  `Tot(L₁)`, `Tot(L₂)` glued along their zero sections (`A = O_C ⊕ ⨁_{j ≥ 1} (L₁^{-j} ⊕ L₂^{-j})` with
  `L₁^{-i}·L₂^{-j} = 0`; affine over `C`, of finite type), `sec` the common zero section, `r = 1`, `n = 1`.
* `hloc` holds: based 1-jets of `Z/C` at `sec` are `Hom_{O_C}(I/I², -)` with `I/I² = L₁^∨ ⊕ L₂^∨` locally free of
  rank 2 (Stacks 0474 needs no smoothness), so `S = Sym(I/I²)` is locally `O_U[x_{0,0}, x_{1,0}]` with both variables
  of weight 1.
* `E = sec^*T_{Z/C} ≅ O_C²`: locally `B = R[x,y]/(xy)`, `Der_R(B) = xR[x]∂_x ⊕ yR[y]∂_y = B·D₁ ⊕ B·D₂` with the two
  **Euler fields** `D₁ = x∂_x`, `D₂ = y∂_y`, which are global sections of `T_{Z/C}`; so `hE`, `hEZ` hold with
  `E = O_C²`.
* But `S_1/I^{(2)}_1 = S_1 = I/I² = O(-1) ⊕ O ≇ O² = E^∨` (different `h⁰`). The natural map
  `sec^*T_{Z/C} → (I/I²)^∨` is even zero here (the tangent vectors at a singular point pair trivially with `m/m²`).
The same example refutes the unhypothesized form of `deformedJetAlgebra_restrictToLambda_zero` (for `r = 1` the fibre
at `λ = 0` is `gr_{S_+}S = Sym(I/I²)`, not `Sym(E^∨)`) and of the third component of `deformedJetAlgebra_spec`; all
of them need the paper's standing hypothesis that `sec` lands in an open `Zx ⊆ Z` smooth over `C` of relative
dimension `n+1` (§2 of the paper, `𝒵^×`), exactly as `jetGradedAlgebra_isLocallyWeightedPolynomial` and
`jetGradedAlgebra_localWeightedChart_of_smooth` carry it. Under that hypothesis `hloc` is a consequence, so it is
dropped here.

## Route (helper modules `JetLinearPiece_Defs`, `_Generation`, `_FreeRank`, `_Derivation`, `_Naturality`)

Notation: `Ω' := sec^*Ω_{Z/C}`, `S := (jetGradedAlgebra Z sec hs r).1`, `L := cokernel (S.irrelevantPow 2 (q+1)).2`
(`= S_{q+1}/I^{(2)}_{q+1}`), and for an affine `U ⊆ C`: `A := Γ(C, U)`, `B := Γ(Z, π⁻¹U)` (affine, `π` is affine),
`ε := sec^♯ : B → A` (`relativeJetScheme.augmentation`), `J := J_r(B, ε) = BasedJetAlgebra ε r` (the chart ring,
`relativeJetScheme.chartEquiv : J ≃+* Γ(π⁻¹U, O_J)`), `d_q b := coeffClass ε r (q+1) b ∈ J` (the `(q+1)`-st jet
coefficient of `b`, weight `q+1`).

* `jetLinearPiece.omegaSection U b := (db)|_sec ∈ Γ(U, Ω')` and `jetLinearPiece.jetSection U m : Γ(U, S_m) → J`
  (canonical, injective, image `grading ε r m`) name the two kinds of sections everything is phrased in.
* `jetLinearPiece.IsCoefficientHom q θ`: the morphism `θ : Ω' ⟶ L` sends `(db)|_sec ↦ [d_q b]` over every affine `U`.
* `AlgebraicGeometry.Scheme.Modules.exists_hom_of_affine_sectionMaps` (generic sheaf theory): a natural family of
  `Γ(X,U)`-linear section maps on the affine opens glues to a morphism of `O_X`-modules.
* `BasedJetAlgebra.coeffClass_mul_sub_mem_irrPow` (algebra): Leibniz modulo decomposables,
  `d_q(bb') ≡ ε(b) d_q b' + ε(b') d_q b mod I^{(2)}_{q+1}`.
* `jetGradedAlgebra_linearPiece_exists_affine_coefficientMaps`: the natural family `θ_U : Γ(U, Ω') → Γ(U, L)`,
  `(db)|_sec ↦ [d_q b]`, on affine opens (`jetLinearPiece.coeffMap`, `coeffMap_char`, `coeffMap_restrict`).
* `jetGradedAlgebra_linearPiece_exists_coefficientHom`: `θ` exists.
* `jetGradedAlgebra_linearPiece_coefficientHom_app_bijective`: on an affine `U` with `E|_U` trivial, `θ.app U` is
  bijective (surjective by generation, then Orzech; `jetLinearPiece.coefficientHom_app_bijective`).
* `jetGradedAlgebra_linearPiece_iso_pullback_omega`: `L ≅ Ω'` by `isIso_of_affineOpens_cover_bijective` on the frame
  cover `coneTangentBundle_exists_affine_frame`.
* `dual_coneTangentBundle_iso_pullback_omega` (`…_LinearPieceDual_OmegaDual`): `E^∨ ≅ Ω'` on the smooth locus.
* `jetGradedAlgebra_linearPiece_iso_dual_of_smooth` composes the two.

Source: §2 of the paper (eq. (2.7): the linear part of the jet coordinate transition is the Jacobian;
eq. (2.5): `I/I² = E^∨|_U`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Generic ingredients (proved) -/

/-- **Gluing a morphism of `O_X`-modules from section maps on the affine opens** (Stacks 009A/04TN; Mathlib
`TopCat.Sheaf.restrictHomEquivHom`). Given, for every affine open `U`, a `Γ(X, U)`-linear map
`f U : Γ(M, U) → Γ(N, U)`, compatible with restriction between affine opens, there is a morphism `g : M ⟶ N` with
`g.app U = f U` for every affine `U`.

Proof: the affine opens form a basis (`Scheme.isBasis_affineOpens`); the `f U` are the components of a natural
transformation `α` between the restrictions of the abelian presheaves of `M`, `N` to that basis (naturality is `hf`);
`restrictHomEquivHom` extends `α` to `φ : M.presheaf ⟶ N.presheaf` with `φ.app U = f U` on the basis
(`extend_hom_app`). `φ` is `O_X`-linear: for an arbitrary open `V`, `φ(r • m) = r • φ m` holds after restriction to every
affine `W ⊆ V` (naturality of `φ`, `map_smul`, linearity of `f W`), and the affine `W ⊆ V` cover `V`, so it holds on `V`
(`eq_of_locally_eq'`). `PresheafOfModules.homMk` turns `φ` into a morphism of `O_X`-modules.
Edge cases: `X = ∅` (no affine opens except `⊥`; `g` is the zero morphism); `M = 0`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_hom_of_affine_sectionMaps {X : AlgebraicGeometry.Scheme.{u}}
    (M N : X.Modules)
    (f : ∀ U : X.affineOpens, Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1))
    (hf : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (m : Γ(M, U.1)),
      N.presheaf.map (homOfLE h).op (f U m) = f V (M.presheaf.map (homOfLE h).op m)) :
    ∃ g : M ⟶ N, ∀ (U : X.affineOpens) (m : Γ(M, U.1)), (g.app U.1).hom m = f U m := by
  let B : X.affineOpens → X.Opens := fun U => U.1
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    show TopologicalSpace.Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1))
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  let α : (CategoryTheory.inducedFunctor B).op ⋙ M.presheaf ⟶
      (CategoryTheory.inducedFunctor B).op ⋙ N.presheaf :=
    { app := fun p => AddCommGrpCat.ofHom (f p.unop).toAddMonoidHom
      naturality := by
        intro p q h
        ext m
        change (f q.unop) (M.presheaf.map _ m) = N.presheaf.map _ ((f p.unop) m)
        exact (hf p.unop q.unop (leOfHom h.unop.hom) m).symm }
  let φ : M.presheaf ⟶ N.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB α
  have hφ : ∀ U : X.affineOpens, φ.app (op U.1) = AddCommGrpCat.ofHom (f U).toAddMonoidHom := fun U =>
    TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB α U
  have hlin : ∀ (V : X.Opens) (r : Γ(X, V)) (m : Γ(M, V)),
      φ.app (op V) (r • m) = r • φ.app (op V) m := by
    intro V r m
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
      (fun W : {W : X.affineOpens // W.1 ≤ V} => W.1.1) V (fun W => homOfLE W.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨W, hWaff, hxW, hWV⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hWaff⟩, hWV⟩, hxW⟩
    · intro W
      have nat := fun y => ConcreteCategory.congr_hom (φ.naturality (homOfLE W.2).op) y
      simp only [ConcreteCategory.comp_apply] at nat
      change N.presheaf.map _ (φ.app (op V) (r • m)) = N.presheaf.map _ (r • φ.app (op V) m)
      rw [← nat, AlgebraicGeometry.Scheme.Modules.map_smul, AlgebraicGeometry.Scheme.Modules.map_smul,
        ← nat, hφ W.1]
      exact (f W.1).map_smul _ _
  refine ⟨SheafOfModules.Hom.mk (PresheafOfModules.homMk φ (fun V r m => hlin V.unop r m)), ?_⟩
  intro U m
  show φ.app (op U.1) m = f U m
  rw [hφ U]
  rfl

/-- **Leibniz modulo decomposables** in the based jet algebra `J_r(B, ε)`: for `q < r`,
`D_{q+1}(b b') - (ε(b) D_{q+1} b' + ε(b') D_{q+1} b) ∈ I^{(2)}_{q+1} = (J_+)² ∩ J_{q+1}`
(`ReesAlgebra.irrPow (BasedJetAlgebra.grading ε r) 2 (q+1)`).

Proof: `coeffClass_mul` gives `D_{q+1}(bb') = Σ_{i+j=q+1} D_i b · D_j b'`; the terms `(0, q+1)` and `(q+1, 0)` are
`ε(b) D_{q+1} b'` and `ε(b') D_{q+1} b` (`coeffClass_zero_order`, `D_0 = ε`), and every other term has `i, j ≥ 1`,
so `D_i b ∈ J_i ⊆ J_+` and `D_j b' ∈ J_j ⊆ J_+` (`coeffClass_mem_grading`, `HomogeneousIdeal.mem_irrelevant_of_mem`),
whence `D_i b · D_j b' ∈ (J_+)² ∩ J_{q+1}` (`ReesAlgebra.irrPow_mul`). Source: §2 of the paper, eq. (2.7)
(the linear part of the jet coordinates). -/
theorem BasedJetAlgebra.coeffClass_mul_sub_mem_irrPow {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r q : ℕ) (hq : q < r) (b b' : B) :
    BasedJetAlgebra.coeffClass ε r (q + 1) (b * b') -
      (algebraMap R (BasedJetAlgebra ε r) (ε b) * BasedJetAlgebra.coeffClass ε r (q + 1) b' +
        algebraMap R (BasedJetAlgebra ε r) (ε b') * BasedJetAlgebra.coeffClass ε r (q + 1) b) ∈
      ReesAlgebra.irrPow (BasedJetAlgebra.grading ε r) 2 (q + 1) :=
  BasedJetAlgebra.coeffClass_mul_sub_mem_irrPow_two ε r q hq b b'

/-! ## The coefficient morphism `θ_q : sec^*Ω_{Z/C} ⟶ S_{q+1}/I^{(2)}_{q+1}` -/

section CoefficientHom

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) [AlgebraicGeometry.IsClosedImmersion sec] (r : ℕ)

/-! The definitions `jetLinearPiece.omegaSection`, `jetLinearPiece.jetSection`, `jetLinearPiece.IsCoefficientHom` and the
linear-algebra facts about `jetSection` (linearity, injectivity, image `= grading ε_U r m`, the graded ring homomorphism
`Ψ⁻¹ = jetLinearPiece.toSectionsRing` and `exists_irrelevantPow_app_eq_of_jetSection_mem_irrPow`) live in
`JetLinearPiece_Defs`. -/

/-- **The local coefficient maps.** For every affine `U ⊆ C` there is a `Γ(C,U)`-linear map
`θ_U : Γ(U, sec^*Ω_{Z/C}) → Γ(U, L_{q+1})`, `(db)|_sec ↦ [d_q b]`, and the family is natural in `U`.
Source: §2 of the paper, eq. (2.7) (the linear part of the `(q+1)`-st jet coefficient is a derivation);
Stacks 01I9 (sections of a pullback over affines), 01UT (`Γ(π⁻¹U, Ω_{Z/C}) = Ω_{B/A}`), 00RM (universal property of
Kähler differentials).

Proof sketch. Fix an affine `U`; `A := Γ(C,U)`, `B := Γ(Z, π⁻¹U)` (`π⁻¹U` is affine, `π` being affine),
`ε := augmentation Z sec hs U = sec^♯ : B → A`, `J := J_r(B, ε)`, `S := (jetGradedAlgebra Z sec hs r).1`,
`ι₂ := (S.irrelevantPow 2 (q+1)).2 : I → S_{q+1}`, `L := cokernel ι₂`, `π_L := cokernel.π ι₂`.
(1) *Sections of `S_{q+1}` in `J`* (`JetLinearPiece_Defs`). `js := jetSection U (q+1) : Γ(U, S_{q+1}) → J` is additive,
injective (`weightPartιApp_injective`), `A`-linear, with image `grading ε r (q+1)`
(`weightDefect_app_chartEquiv_eq_zero_iff`, `exists_kernel_section`, `kernel_ι_app_apply`); let
`σ : grading ε r (q+1) → Γ(U, S_{q+1})` be its inverse.
(2) *The derivation* (`JetLinearPiece_Derivation`). `D : B → Γ(U, L)`, `D b := π_L.app U (σ (d_q b))`, is additive
(`coeffClass_add`), `A`-linear (`coeffClass_smul`) and Leibniz for the `B`-module structure of `Γ(U, L)` through `ε`: by
`coeffClass_mul_sub_mem_irrPow` the defect lies in `irrPow (grading ε r) 2 (q+1)`, and such elements are killed by
`π_L.app U ∘ σ` (through the graded ring isomorphism `Ψ⁻¹ = toSectionsRing`, `ReesAlgebra.map_mem_irrPow`,
`irrelevantPow_app_range_iff` and `cokernel.condition`). So `D` is an `A`-derivation.
(3) *Base change.* `D = D̄ ∘ d` with `D̄ := D.liftKaehlerDifferential : Ω[B⁄A] →ₗ[B] Γ(U, L)`, extended `A`-linearly to
`A ⊗_B Ω[B⁄A]`; identify `A ⊗_B Ω[B⁄A] ≅ Γ(U, sec^*Ω_{Z/C})` via `Omega_appIso` (Stacks 01UT) and
`isIso_transpose_pullbackSectionsNative` (Stacks 01I9), and put `θ_U := D̃ ∘ (that isomorphism)⁻¹`. Then
`θ_U (omegaSection U b) = D b`, which is the characterisation (`coeffMap_char`).
(4) *Naturality for affine `V ≤ U`* (`JetLinearPiece_Naturality`). Both composites are `A`-linear, so it suffices to
compare them on the generators `omegaSection U b`, using the restriction lemmas for `omegaSection` and for the classes
`[d_q b]`; the naturality of the chart reading `χ_U (d_q b)` in the open is obtained from the global universal jet
`u : J ×_k D_r → Z` (`χ_U (d_q b)` is the `t^{q+1}`-coefficient of `u^♯ b`, `chartEquiv_coeffClass`,
`jetCoordSection_restrict`), since `chartSections_comp_map` only covers basic-open inclusions.
Edge cases: `U = ⊥` (all modules zero); `q = 0`: `irrPow 2 1 = 0`, `L_1 = S_1`, and step (2) is exact Leibniz;
`r = 0`: no `q`. -/
theorem jetGradedAlgebra_linearPiece_exists_affine_coefficientMaps (q : Fin r) :
    ∃ f : ∀ U : C.toScheme.affineOpens,
        Γ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom), U.1)
          →ₗ[Γ(C.toScheme, U.1)]
        Γ(CategoryTheory.Limits.cokernel
          ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1),
      (∀ (U V : C.toScheme.affineOpens) (h : V.1 ≤ U.1)
        (m : Γ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom), U.1)),
        (CategoryTheory.Limits.cokernel
          ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).presheaf.map (homOfLE h).op
            (f U m) =
          f V (((AlgebraicGeometry.Scheme.Modules.pullback sec).obj
            (AlgebraicGeometry.Omega Z.hom)).presheaf.map (homOfLE h).op m)) ∧
      (∀ (U : C.toScheme.affineOpens) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
        (x : ((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1)).val.obj (Opposite.op U.1)),
        (letI := relativeJetScheme.sectionsAlgebra Z U.1;
          jetLinearPiece.jetSection Z sec hs r U (q.1 + 1) x =
            BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z sec hs U.1) r (q.1 + 1) b) →
        f U (jetLinearPiece.omegaSection Z sec hs U.1 b) =
          ((CategoryTheory.Limits.cokernel.π
            ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom x) :=
  ⟨fun U => jetLinearPiece.coeffMap Z sec hs r U q,
    fun U V h m => jetLinearPiece.coeffMap_restrict Z sec hs r q U V h m,
    fun U b x hx => jetLinearPiece.coeffMap_char Z sec hs r U q b x hx⟩

/-- **The coefficient morphism exists**: glue the local coefficient maps of
`jetGradedAlgebra_linearPiece_exists_affine_coefficientMaps` with `exists_hom_of_affine_sectionMaps`. -/
theorem jetGradedAlgebra_linearPiece_exists_coefficientHom (q : Fin r) :
    ∃ θ : (AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom) ⟶
        CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2,
      jetLinearPiece.IsCoefficientHom Z sec hs r q θ := by
  obtain ⟨f, hnat, hchar⟩ := jetGradedAlgebra_linearPiece_exists_affine_coefficientMaps Z sec hs r q
  obtain ⟨g, hg⟩ := AlgebraicGeometry.Scheme.Modules.exists_hom_of_affine_sectionMaps _ _ f hnat
  refine ⟨g, ?_⟩
  intro U b x hx
  rw [hg U]
  exact hchar U b x hx

/-- **The coefficient morphism is bijective on the sections over an affine `U` on which `E = sec^*T_{Z/C}` is
trivial.** Source: §2 of the paper (eq. (2.5), eq. (2.7): jet coordinates on a chart, the
linear part of the transition is the Jacobian).

Proof sketch (notation as in `jetGradedAlgebra_linearPiece_exists_affine_coefficientMaps`). No étale coordinates and
no Jacobian are needed: surjectivity is pure algebra, and injectivity follows from a rank count.
(1) *`Γ(U, L)` is generated over `A` by the classes `[d_q b]`, `b ∈ B`* (`JetLinearPiece_Generation`).
`Γ(U, π_L) : Γ(U, S_{q+1}) → Γ(U, L)` is surjective (`cokernel.π` is an epimorphism between quasi-coherent modules and
`Γ(U, -)` is exact on quasi-coherent modules over the affine `U`, Stacks 01XB); `Γ(U, S_{q+1}) ≅ grading ε r (q+1)` via
`js`, and `grading ε r (q+1)` is the `A`-span of the monomials `∏ d_{q_i} b_i` with `Σ (q_i+1) = q+1`
(`BasedJetAlgebra.mem_grading_iff`); a monomial with at least two factors lies in `(J_+)² ∩ J_{q+1}`, hence in the
kernel of `π_L.app U ∘ σ`, and the monomials with exactly one factor are the `d_q b`.
(2) *Surjectivity of `θ.app U`.* By the characterisation `hθ`, `θ.app U (omegaSection U b) = [d_q b]` for every `b ∈ B`;
with (1), `θ.app U` is surjective (`jetLinearPiece.coefficientHom_app_surjective`).
(3) *Both sides are free `A`-modules of rank `n+1`* (`JetLinearPiece_FreeRank`). `Γ(U, sec^*Ω_{Z/C})` is free of rank
`n+1` via `dual_coneTangentBundle_iso_pullback_omega` and the trivialization of `E|_U`
(`exists_basis_omega_sections`). `Γ(U, L)`: `jetGradedAlgebra_localWeightedChart_of_smooth` gives a graded,
unit-compatible ring isomorphism `e : Γ(U, S) ≃+* A[x_{a,q'}]` (`x_{a,q'}` of weight `q'+1`); under it the image of
`Γ(U, ι₂)` is the span of the monomials of weight `q+1` and degree `≥ 2` (`irrelevantPow_app_range_iff`,
`irrPow_weightedHomogeneousSubmodule_eq_span`), so `Γ(U, L)` is free on the classes of the `n+1` variables `x_{a,q}`
(`exists_basis_linearPiece_sections`, via `MvPolynomial.exists_basis_of_weightedHomogeneous_quotient`).
(4) *Injectivity (Orzech).* Choosing bases, `θ.app U` becomes a surjective `A`-linear endomorphism of the finitely
generated module `A^{n+1}`, hence injective (`OrzechProperty.injective_of_surjective_endomorphism`;
`coefficientHom_app_injective`). So `θ.app U` is bijective (`jetLinearPiece.coefficientHom_app_bijective`).
Edge cases: `U = ⊥` (zero modules, trivially bijective); `n = 0` (rank 1); `q = 0` (`L_1 = S_1`, generated by the
`d_0 b`, free on `x_{a,0}`). -/
theorem jetGradedAlgebra_linearPiece_coefficientHom_app_bijective
    (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (q : Fin r)
    (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle Z.hom sec hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1)))))
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom) ⟶
      CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2)
    (hθ : jetLinearPiece.IsCoefficientHom Z sec hs r q θ) :
    Function.Bijective (θ.app U.1).hom :=
  jetLinearPiece.coefficientHom_app_bijective Z sec hs r Zx hsZx n q U htriv θ hθ

end CoefficientHom

/-- **The linear piece of the jet algebra in weight `q+1` is `sec^*Ω_{Z/C}`** — the one genuinely jet-specific input of
`deformedJetAlgebra_restrictToLambda_zero`. `S := (jetGradedAlgebra Z sec hs r).1`,
`L_{q+1} := S_{q+1}/I^{(2)}_{q+1} = cokernel (S.irrelevantPow 2 (q+1)).2`.
Source: §2 of the paper, eq. (2.7) (the transition functions of the jet coordinates of order `q+1` have
linear part the Jacobian of the coordinate change on `Z` along `sec`).

Assembled from `jetGradedAlgebra_linearPiece_exists_coefficientHom` (the coefficient morphism
`θ_q : sec^*Ω_{Z/C} ⟶ L_{q+1}`, `(db)|_sec ↦ [d_q b]`) and `jetGradedAlgebra_linearPiece_coefficientHom_app_bijective`
(bijective on the sections over every affine `U` with `E|_U` trivial): these `U` cover `C`
(`coneTangentBundle_exists_affine_frame`), both modules are quasi-coherent (`isQuasicoherent_pullback` +
`Omega_isQuasicoherent`; `isQuasicoherent_kernel` (Stacks 01IC) with `irrelevantPow_isQuasicoherent`), so `θ_q` is an
isomorphism (`isIso_of_affineOpens_cover_bijective`), and the statement is its inverse.
Edge cases: `r = 0` (no `q`, vacuous); `q = 0`: `I^{(2)}_1 = 0` and the statement is `S_1 ≅ sec^*Ω` (based 1-jets are
`(I/I²)^∨`, Stacks 0474 — true without smoothness); `n = 0` (`Z` a curve over `C`); `C` empty. -/
theorem jetGradedAlgebra_linearPiece_iso_pullback_omega {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) [AlgebraicGeometry.IsClosedImmersion sec]
    (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (r : ℕ) (q : Fin r) :
    Nonempty (CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2 ≅
      (AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom)) := by
  classical
  obtain ⟨θ, hθ⟩ := jetGradedAlgebra_linearPiece_exists_coefficientHom Z sec hs r q
  have : ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom)).IsQuasicoherent := by
    have := AlgebraicGeometry.Omega_isQuasicoherent Z.hom
    infer_instance
  have : (CategoryTheory.Limits.cokernel
      ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).IsQuasicoherent := by
    have := (jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow_isQuasicoherent 2 (q.1 + 1)
    have := (jetGradedAlgebra (k := k) Z sec hs r).1.quasicoherent (q.1 + 1)
    exact (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel _).2
  choose U hU hframe using fun x : C.toScheme =>
    coneTangentBundle_exists_affine_frame Z.hom sec hs Zx hsZx n x
  have : IsIso θ :=
    AlgebraicGeometry.Scheme.Modules.isIso_of_affineOpens_cover_bijective θ (fun x => (U x).1)
      (fun x => (U x).2) (fun x => ⟨x, hU x⟩)
      (fun x => jetGradedAlgebra_linearPiece_coefficientHom_app_bijective Z sec hs r Zx hsZx n q (U x)
        (hframe x) θ hθ)
  exact ⟨(asIso θ).symm⟩

/-- **The linear piece of the jet algebra in weight `q+1` is `E^∨`, `E = sec^*T_{Z/C}`**, under the paper's hypothesis
that `sec` lands in an open `Zx ⊆ Z` smooth over `C` of relative dimension `n+1` (§2 of the paper). Assembled from the
jet-specific `jetGradedAlgebra_linearPiece_iso_pullback_omega` (`S_{q+1}/I^{(2)}_{q+1} ≅ sec^*Ω_{Z/C}`) and
`dual_coneTangentBundle_iso_pullback_omega` (`E^∨ ≅ sec^*Ω_{Z/C}`). The version without smoothness is false; see the
module docstring. -/
theorem jetGradedAlgebra_linearPiece_iso_dual_of_smooth {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) [AlgebraicGeometry.IsClosedImmersion sec]
    (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (r : ℕ) (q : Fin r) :
    Nonempty (CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2 ≅
      AlgebraicGeometry.Scheme.Modules.dual (coneTangentBundle Z.hom sec hs)) := by
  have : AlgebraicGeometry.Smooth (Zx.ι ≫ Z.hom) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth (n + 1) (Zx.ι ≫ Z.hom)
  obtain ⟨e₁⟩ := jetGradedAlgebra_linearPiece_iso_pullback_omega Z sec hs Zx hsZx n r q
  obtain ⟨e₂⟩ := dual_coneTangentBundle_iso_pullback_omega Z.hom sec hs Zx hsZx
  exact ⟨e₁ ≪≫ e₂.symm⟩

end
