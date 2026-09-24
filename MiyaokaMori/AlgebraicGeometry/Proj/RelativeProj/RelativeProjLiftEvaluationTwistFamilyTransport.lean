import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAbsolute
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleRestriction
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyTransportSections
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyTransportEval
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyTransportShape
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyTransportMulShape
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIso
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # Transport between a piece of `relativeProj.lift` and the absolute `Proj.fromOfGlobalSections`

Companion of `RelativeProjLiftEvaluationTwistFamily.lean`. Notation: `τ := relativeProj.lift S f M D`, `π := (relativeProj S).hom`, `P := Proj_X S`,
`W : X.affineOpens`, `𝒜 := S.sectionsGrading W`, `ρ := (affineIso S W).inv ≫ (π⁻¹W).ι : Proj 𝒜 ⟶ P`
(`chartEmbedding`).

## Generalized pieces
A *generalized piece* is an open `V ≤ U ⊓ f⁻¹W` of `T` (`U` a trivializing open of `M`, `e : M|_U ≅ O_U`), together
with `Φ_V := pieceRingHom : A(W) →+* Γ(V, O)` (the general form `liftLocalRingHomAux` at `V.ι`, equal to
`liftLocalRingHom` restricted to `V`: `pieceRingHom_eq`) and `φ_V := pieceMap := Proj.fromOfGlobalSections 𝒜 Φ_V`.
The pieces `V'` of the definition of `lift` satisfy `V'.ι ≫ τ = φ_{V'} ≫ ρ` (`liftLocal_eq_pieceMap_comp`), and so
does every open `V ≤ V'` (`ι_lift_eq_pieceMap_comp_of_le`, via `fromOfGlobalSections_naturality`) — this is what
lets the uniqueness statement work on an arbitrary open `V` of a piece without any affineness.

## The two transport isomorphisms (all from the library, no new mathematics)
* `twistTransport n : (τ^*O(n))|_V ≅ φ_V^*O_{Proj 𝒜}(n)` — `restrictFunctorIsoPullback`, `pullbackComp`,
  `pullbackCongr hτ`, and `chartTwistIso : ρ^*O(n) ≅ O_{Proj 𝒜}(n)` (from `twistAffineIso`, Stacks 01NR);
* `powTriv n : (M^{⊗n})|_V ⟶ O_V`, an isomorphism — `pullbackMonoidalPow`, `monoidalPowMap` of the trivialization,
  `unitPowCollapse` (the tail of `liftLocalHomAux`).

## The dictionary (five lemmas)
Under these isomorphisms: `α_n` becomes the pulled-back global section `a/1` (`twistTransport_evalHom`),
`β_n` becomes `Φ_V` (`powTriv_dataHom`), the relative twist multiplication `μ` becomes the absolute one
(`twistTransport_twistMulHom`), and `monoidalPowCat` becomes multiplication in `Γ(V, O)` (`powTriv_monoidalPowCat`).
`span_range_pullbackSectionsOn_eq_top` (from Stacks 01I9, `isIso_transpose_pullbackSectionsNative`) says
that the pulled-back sections of a quasi-coherent module generate over affine opens; it is what reduces the
factorization (F) to the generators `η(x)`.

**Kernel performance.** `chartTwistIso` and `twistTransport` are *defined* as the variable-level shapes
`Modules.chartIsoShape` / `Modules.transportIsoShape` (`…Transport_Shape.lean`) applied to atomic arguments, and every
statement about them is a first-order instance of a variable-level lemma (`…Transport_Shape.lean`,
`…Transport_MulShape.lean`), entered through the top-level `rfl` bridges `chartTwistIso_eq_shape` /
`twistTransport_eq_shape` with `rw` (not `unfold`/`delta`, which leave the kernel to identify the two spellings under
`Iso.hom`/`Hom.app` and cost 45–60+ s).

The morphisms `α_n = LiftData.evalHom`, `β_n = LiftData.dataHom`, `μ = LiftData.twistMulHom` are defined in
`RelativeProjLiftEvaluationTwistFamily.lean` (which imports this file); here they appear as their defining composites
(`(pullbackComp τ π).inv ≫ τ^*(evaluation)`, `(pullbackCongr lift_hom).hom ≫ Ψ_n`, `δ⁻¹ ≫ τ^*(tITO.inv ≫ twistMul ≫ eqToHom)`),
to which they are definitionally equal. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-! ## Pulled-back sections of a quasi-coherent module generate (Stacks 01I9) -/

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- Sections of the unit sheaf `O_Y` over `B`, read as elements of `Γ(Y, B)` (an identity coercion; it fixes the
type so that ring operations on `Γ(Y, B)` can be applied). -/
def unitSectionsToRing (Y : AlgebraicGeometry.Scheme.{u}) (B : Y.Opens)
    (x : Γ(SheafOfModules.unit Y.ringCatSheaf, B)) : Γ(Y, B) := x

/-- **Pulled-back sections generate over affine opens** (Stacks 01I9). For `g : Y ⟶ X`, `M` quasi-coherent on `X`,
`V ⊆ X` and `V' ⊆ g⁻¹V` affine opens, the `Γ(Y, V')`-span of the pulled-back sections
`pullbackSectionsOn g M V V' h x = (g^*x)|_{V'}`, `x ∈ Γ(M, V)`, is all of `Γ(g^*M, V')`.

Proof: `isIso_transpose_pullbackSectionsNative` says that the
transpose `Γ(Y, V') ⊗_{Γ(X, V)} Γ(M, V) → Γ(g^*M, V')`, `t ⊗ x ↦ t • (g^*x)|_{V'}`, is an isomorphism, in particular
surjective; every element of the tensor product is a finite sum of pure tensors (`TensorProduct.induction_on`), and
each `t • (g^*x)|_{V'}` lies in the span. -/
theorem span_range_pullbackSectionsOn_eq_top (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] (V : X.Opens)
    (hV : AlgebraicGeometry.IsAffineOpen V) (V' : Y.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V')
    (h : V' ≤ g ⁻¹ᵁ V) :
    Submodule.span Γ(Y, V')
      (Set.range (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn g M V V' h)) = ⊤ := by
  rw [eq_top_iff]
  rintro s -
  have hiso := AlgebraicGeometry.Scheme.Modules.isIso_transpose_pullbackSectionsNative g M V hV V' hV' h
  set t := ((ModuleCat.extendRestrictScalarsAdj (g.appLE V V' h).hom).homEquiv _ _).symm
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionsNative g M V V' h) with ht
  have hsurj : Function.Surjective t.hom := (ConcreteCategory.bijective_of_isIso t).2
  obtain ⟨w, rfl⟩ := hsurj s
  let _ : Algebra Γ(X, V) Γ(Y, V') := (g.appLE V V' h).hom.toAlgebra
  have key : ∀ (r : Γ(Y, V')) (x : Γ(M, V)),
      t.hom (r ⊗ₜ[Γ(X, V)] x) = r • AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn g M V V' h x := by
    intro r x
    change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (g.appLE V V' h).hom
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionsNative g M V V' h)).hom (r ⊗ₜ[Γ(X, V)] x) = _
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
    rfl
  change (t.hom w) ∈ _
  induction w using TensorProduct.induction_on with
  | zero => erw [map_zero]; exact Submodule.zero_mem _
  | tmul r x =>
    rw [key r x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add w₁ w₂ h₁ h₂ => erw [map_add]; exact Submodule.add_mem _ h₁ h₂

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T : AlgebraicGeometry.Scheme.{u}}


/-! ## The chart embedding `ρ : Proj A(W) ⟶ Proj_X S` and the twist on the chart -/

/-- `ρ := (affineIso S W).inv ≫ (π⁻¹W).ι : Proj A(W) ⟶ Proj_X S`, the open immersion of the chart over the affine
open `W` (Stacks 01NQ). -/
def chartEmbedding (S : X.GradedQCAlgebra) (W : X.affineOpens) :
    AlgebraicGeometry.Proj (S.sectionsGrading W.1) ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left :=
  (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv ≫
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι

/-- `ρ^*O(n) ≅ O_{Proj A(W)}(n)` (Stacks 01NR): `ρ^*O(n) ≅ e⁻¹^*(ι^*O(n)) ≅ e⁻¹^*(O(n)|_{π⁻¹W}) ≅
e⁻¹^*(e^*O_{A(W)}(n)) ≅ (e⁻¹ ≫ e)^*O_{A(W)}(n) = O_{A(W)}(n)`, with `twistAffineIso S W n` in the middle.
Defined as the variable-level shape `Modules.chartIsoShape` (`…Transport_Shape.lean`) applied to the chart data, so
that statements about it are first-order instances of the shape lemmas (kernel-cheap). -/
def chartTwistIso (S : X.GradedQCAlgebra) (W : X.affineOpens) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S n) ≅
      AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) n :=
  AlgebraicGeometry.Scheme.Modules.chartIsoShape ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S W) (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)
    rfl (AlgebraicGeometry.Scheme.relativeProj.twist S n) (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) n)
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W n)

/-- `chartTwistIso` is the chart shape applied to the chart data (one delta step). Statements about
`chartTwistIso` are proved by `rw [chartTwistIso_eq_shape]` and the shape lemma: the rewrite produces a genuine
cast, whereas `unfold`/`delta` are definitional relabelings after which the kernel has to identify the two
spellings under the `Iso.hom`/`Hom.app` heads and normalises the whole `Modules.pullback` construction
(more than 60 s versus less than 1 s). -/
theorem chartTwistIso_eq_shape (S : X.GradedQCAlgebra) (W : X.affineOpens) (n : ℤ) :
    AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W n =
      AlgebraicGeometry.Scheme.Modules.chartIsoShape ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι
        (AlgebraicGeometry.Scheme.relativeProj.affineIso S W) (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)
        rfl (AlgebraicGeometry.Scheme.relativeProj.twist S n) (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) n)
        (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W n) := rfl

/-- **The chart twist isomorphism on the pulled-back evaluation section** (leaf of D-α). For `U` an open of
`Proj A(W)` with `U ≤ ρ⁻¹(π⁻¹W)` and `x ∈ Γ(W, S_n)`:
`chartTwistIso((ρ^*(evaluationLocal S n W x))|_U) = twistSection 𝒜 (sectionsOf x)|_U`.

**Natural-language proof (complete; Stacks 01MN, 01NR).** Write `e := affineIso S W`, `ι_W := (π⁻¹W).ι`,
`s := evaluationLocal S n W x`, `t := twistSection 𝒜 (sectionsOf x)`. `chartTwistIso = J₁ ≫ J₂ ≫ J₃ ≫ J₄ ≫ J₅` with
`J₁ = ((pullbackComp e.inv ι_W).app N)⁻¹`, `J₂ = e.inv^*((rFIP ι_W)⁻¹ ≫ twistAffineIso)`, `J₃ = (pullbackComp e.inv e.hom).app G`,
`J₄ = (pullbackCongr e.inv_hom_id).app G`, `J₅ = (pullbackId).app G`. On `(ρ^*s)|_U`:
`J₁` gives `(e.inv^*(η_{ι_W} s))|_U` (`pullbackComp_inv_app_pullbackSectionsOn`); `J₂` acts inside the pulled-back
section (`pullback_map_app_pullbackSectionsOn_bc`) and `twistAffineIso_hom_app_unit_evaluationLocal`
(`…TransportEval.lean`) turns `(rFIP)⁻¹ ≫ twistAffineIso` on `η_{ι_W} s` into `(η_e t)|_{ι_W⁻¹π⁻¹W}`; moving the
restriction (`pullbackSectionsOn_res`), `J₃` gives `((e.inv ≫ e.hom)^*t)|_U` (`pullbackComp_hom_app_pullbackSectionsOn`),
`J₄` gives `(𝟙^*t)|_U` (`pullbackCongr_hom_app_pullbackSectionsOn`) and `J₅` gives `t|_U`
(`pullbackId_hom_app_pullbackSectionsOn_tfam`). ∎

**Formalization.** `chartTwistIso` is `Modules.chartIsoShape` applied to the chart data, and the
statement is the first-order instance of `chartIsoShape_hom_app_pullbackSectionsOn` (`…Transport_Shape.lean`), whose
chart hypothesis is `twistAffineIso_hom_app_unit_evaluationLocal` (`…TransportEval.lean`). (A direct rewrite chain
on the concrete objects elaborates but costs more than 60 s of kernel time.) -/
theorem chartTwistIso_hom_app_pullbackSectionsOn_evaluationLocal (S : X.GradedQCAlgebra) (W : X.affineOpens) (n : ℕ)
    (U : (AlgebraicGeometry.Proj (S.sectionsGrading W.1)).Opens)
    (k : U ≤ AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1)) (x : Γ(S.part n, W.1)) :
    (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W (n : ℤ)).hom.app U
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)) ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1)
          U k (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S n W x)) =
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (AlgebraicGeometry.Proj.twistSection (S.sectionsGrading W.1) (S.sectionsOf W.1 n x).1
          (S.sectionsOf W.1 n x).2) := by
  rw [AlgebraicGeometry.Scheme.relativeProj.chartTwistIso_eq_shape S W (n : ℤ)]
  exact AlgebraicGeometry.Scheme.Modules.chartIsoShape_hom_app_pullbackSectionsOn
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι (AlgebraicGeometry.Scheme.relativeProj.affineIso S W)
    (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) rfl (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)) (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W (n : ℤ))
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1) (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S n W x)
    (AlgebraicGeometry.Proj.twistSection (S.sectionsGrading W.1) (S.sectionsOf W.1 n x).1 (S.sectionsOf W.1 n x).2)
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso_hom_app_unit_evaluationLocal S n W x) U k

/-! ## The chart identity: `twistMul` on the chart is `Proj.twistMul` (Stacks 01NR + 01MO) -/

/-- `twistMul S a b` is the gluing of the local multiplications (one delta step; used with `rw`, see
`chartTwistIso_eq_shape` for why not `unfold`). -/
theorem twistMul_eq_glueHom (S : X.GradedQCAlgebra) (a b : ℤ) :
    AlgebraicGeometry.Scheme.relativeProj.twistMul S a b =
      AlgebraicGeometry.Scheme.Modules.glueHom (fun U : X.affineOpens => (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1)
        (by rw [← AlgebraicGeometry.Scheme.Hom.preimage_iSup, AlgebraicGeometry.iSup_affineOpens_eq_top,
          AlgebraicGeometry.Scheme.Hom.preimage_top])
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S a)
          (AlgebraicGeometry.Scheme.relativeProj.twist S b))
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
        (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b)
        (fun U U' V hU hU' => AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_agree S a b U U' V hU hU') := rfl

/-- **`twistMul` restricted to the chart `π⁻¹W` is the local shape** (Stacks 01NR):
`(twistMul S a b)|_{π⁻¹W} = twistMulLocal S a b W = twistMulLocalShape ι_W e (twist S a) (twist S b) (twist S (a+b))
O(a) O(b) O(a+b) (twistAffineIso a) (twistAffineIso b) (twistAffineIso (a+b)) (Proj.twistMul 𝒜 a b)`
(`restrictFunctor_map_glueHom`, `twistMulLocal_eq_shape`). -/
theorem restrictFunctor_map_twistMul_eq_shape (S : X.GradedQCAlgebra) (W : X.affineOpens) (a b : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι).map
        (AlgebraicGeometry.Scheme.relativeProj.twistMul S a b) =
      AlgebraicGeometry.Scheme.Modules.twistMulLocalShape ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι
        (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom
        (AlgebraicGeometry.Scheme.relativeProj.twist S a) (AlgebraicGeometry.Scheme.relativeProj.twist S b)
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a + b))
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) a) (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) b)
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (a + b))
        (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W a) (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W b)
        (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W (a + b))
        (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading W.1) a b) := by
  rw [AlgebraicGeometry.Scheme.relativeProj.twistMul_eq_glueHom S a b]
  exact (AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_glueHom
    (fun U : X.affineOpens => (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) _ _ _ _ _ W).trans
    (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_eq_shape S a b W)

/-- **The chart identity for `chartTwistIso`** (Stacks 01NR + 01MO): with `ρ := chartEmbedding S W`,
`μ_S := tITO⁻¹ ≫ twistMul S a b ≫ eqToHom` and `μ_𝒜 := tITO⁻¹ ≫ Proj.twistMul 𝒜 a b ≫ eqToHom`,
`δ_ρ⁻¹ ≫ ρ^*μ_S ≫ chartTwistIso(k) = (chartTwistIso a ⊗ chartTwistIso b) ≫ μ_𝒜`, for any `k = a + b`
(the `eqToHom`s transport the index identity; taking `k` as a variable lets `subst` remove them). Proof:
`subst`, `eqToHom_refl`, then `chartTwistIso_eq_shape` three times and the variable-level `chartIsoShape_mul`
with `restrictFunctor_map_twistMul_eq_shape`. -/
theorem chartTwistIso_mul (S : X.GradedQCAlgebra) (W : X.affineOpens) (a b : ℕ) (k : ℤ) (hk : (a : ℤ) + b = k) :
    CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom
        (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)).map
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ))
              (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))).inv ≫
            AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ) ≫
            CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) hk)) ≫
        (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W k).hom =
      ((AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W (a : ℤ)).hom ⊗ₘ
          (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W (b : ℤ)).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (a : ℤ))
            (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (b : ℤ))).inv ≫
        AlgebraicGeometry.Proj.twistMul (S.sectionsGrading W.1) (a : ℤ) (b : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1)) hk) := by
  subst hk
  rw [CategoryTheory.eqToHom_refl, CategoryTheory.eqToHom_refl, Category.comp_id, Category.comp_id,
    AlgebraicGeometry.Scheme.relativeProj.chartTwistIso_eq_shape S W (a : ℤ),
    AlgebraicGeometry.Scheme.relativeProj.chartTwistIso_eq_shape S W (b : ℤ),
    AlgebraicGeometry.Scheme.relativeProj.chartTwistIso_eq_shape S W ((a : ℤ) + b)]
  exact AlgebraicGeometry.Scheme.Modules.chartIsoShape_mul ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S W) (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) rfl
    (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.twist S ((a : ℤ) + b))
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (a : ℤ)) (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (b : ℤ))
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) ((a : ℤ) + b))
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W (a : ℤ)) (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W (b : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W ((a : ℤ) + b))
    (AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ))
    (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading W.1) (a : ℤ) (b : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.restrictFunctor_map_twistMul_eq_shape S W (a : ℤ) (b : ℤ))

/-! ## Generalized pieces -/

section Piece

/-- The trivialization `e` restricted to `V ≤ U ⊓ f⁻¹W`, as `(pullback V.ι).obj M ≅ O_V` (`liftLocalTrivOn`). -/
def pieceTriv (f : T ⟶ X) (M : T.Modules)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) :
    (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalTrivOn f M U e W.1 hle

/-- `V ≤ f⁻¹W`, in the form needed by `liftLocalRingHomAux`. -/
theorem piece_top_le (f : T ⟶ X) (U : T.Opens) (W : X.affineOpens) {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) :
    (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ f) ⁻¹ᵁ W.1 :=
  AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f (hle.trans inf_le_right)

/-- `Φ_V : A(W) = ⊕_m Γ(W, S_m) →+* Γ(V, O)`: the general-form local ring homomorphism at `V.ι` with the restricted
trivialization. It equals `liftLocalRingHom` restricted along `V ≤ U ⊓ f⁻¹W` (`pieceRingHom_eq`). -/
def pieceRingHom (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) : S.sectionsRing W.1 →+* Γ(V.toScheme, ⊤) :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D V.ι
    (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle) W.1
    (AlgebraicGeometry.Scheme.relativeProj.piece_top_le f U W hle)

/-- `Φ_V = res_V ∘ liftLocalRingHom S f M D U e W` (`liftLocal_restrict_ringHom` with `V' := U ⊓ f⁻¹W`). -/
theorem pieceRingHom_eq (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) :
    AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle =
      (T.homOfLE hle).appTop.hom.comp (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom S f M D U e W.1) := by
  have h := AlgebraicGeometry.Scheme.relativeProj.liftLocal_restrict_ringHom S f M D U e W.1 (U ⊓ f ⁻¹ᵁ W.1)
    le_rfl hle
  have hc : (T.homOfLE hle).appTop.hom.comp (T.homOfLE (le_refl (U ⊓ f ⁻¹ᵁ W.1))).appTop.hom =
      (T.homOfLE (hle.trans (le_refl _))).appTop.hom := by
    rw [← CommRingCat.hom_comp, ← AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.homOfLE_homOfLE]
  rw [← RingHom.comp_assoc, hc] at h
  exact h.symm

/-- On a piece `V` that is **affine**, `Φ_V` maps the irrelevant ideal onto the unit ideal
(`liftLocalRingHomAux_map_irrelevant`). -/
theorem pieceRingHom_map_irrelevant (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) (hV : AlgebraicGeometry.IsAffineOpen V) :
    (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤ := by
  have : AlgebraicGeometry.IsAffine V.toScheme := hV
  exact AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant D V.ι _ W _

/-- `φ_V := Proj.fromOfGlobalSections 𝒜 Φ_V : V ⟶ Proj A(W)` (an `abbrev`, so that statements spelled with
`fromOfGlobalSections` — those of `RelativeProjLiftEvaluationTwistFamilyAbsolute.lean` — and statements spelled with
`pieceMap` unify without unfolding anything expensive). -/
abbrev pieceMap (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤) :
    V.toScheme ⟶ AlgebraicGeometry.Proj (S.sectionsGrading W.1) :=
  AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
    (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ

/-- The piece `liftLocal … V'` of the definition of `lift` is `φ_{V'} ≫ ρ`. -/
theorem liftLocal_eq_pieceMap_comp (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V hV hle =
      AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
        AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W := by
  unfold AlgebraicGeometry.Scheme.relativeProj.liftLocal
    AlgebraicGeometry.Scheme.relativeProj.chartEmbedding
  exact congrArg (fun k => k ≫ (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv ≫
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι)
    (AlgebraicGeometry.Proj.fromOfGlobalSections_congr_ringHom (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom_eq S f M D U e W hle).symm _ _)

end Piece

/-- **Every open `V` of a piece `V'` is a generalized piece**: if `V'.ι ≫ τ = liftLocal … V'` then
`V.ι ≫ τ = φ_V ≫ ρ` for every `V ≤ V'` (`fromOfGlobalSections_naturality`:
`homOfLE ≫ fromOfGlobalSections Φ = fromOfGlobalSections (res ∘ Φ)`, and `pieceRingHom_eq`). No affineness of `V`
is needed: the irrelevant-ideal condition `hΦ` for `V` is an explicit hypothesis (it follows from the one of `V'` by
`irrelevant_map_eq_top_comp`, but any proof of it gives the same morphism). -/
theorem ι_lift_eq_pieceMap_comp_of_le (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle' : V' ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hτ : V'.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V' hV' hle')
    {V : T.Opens} (h : V ≤ V')
    (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W (h.trans hle')) = ⊤) :
    V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W (h.trans hle')) hΦ ≫
        AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W := by
  rw [← AlgebraicGeometry.Scheme.homOfLE_ι T h, Category.assoc, hτ]
  unfold AlgebraicGeometry.Scheme.relativeProj.liftLocal
    AlgebraicGeometry.Scheme.relativeProj.chartEmbedding
  rw [← Category.assoc, ← Category.assoc, AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality,
    Category.assoc]
  congr 1
  apply AlgebraicGeometry.Proj.fromOfGlobalSections_congr_ringHom
  rw [AlgebraicGeometry.Scheme.relativeProj.pieceRingHom_eq, ← RingHom.comp_assoc]
  congr 1
  rw [← CommRingCat.hom_comp, ← AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.homOfLE_homOfLE]

/-! ## `Λ_n`: the trivialization of `(M^{⊗n})|_V` (independent of `D`) -/

section PowTriv

/-- `Λ_n : (M^{⊗n})|_V ⟶ O_V`: `(M^{⊗n})|_V ≅ (V.ι)^*(M^{⊗n}) → ((V.ι)^*M)^{⊗n} → O_V^{⊗n} → O_V`
(`pullbackMonoidalPow`, `monoidalPowMap` of the restricted trivialization, `unitPowCollapse` — the tail of
`liftLocalHomAux`). An isomorphism (`isIso_powTriv`). -/
def powTriv (f : T ⟶ X) (M : T.Modules) (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V.ι ⟶ SheafOfModules.unit V.toScheme.ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app
      (AlgebraicGeometry.Scheme.Modules.monoidalPow M n) ≫
    AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow V.ι M n ≫
    AlgebraicGeometry.Scheme.Modules.monoidalPowMap
      (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle).hom n ≫
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse V.toScheme n

theorem isIso_powTriv (f : T ⟶ X) (M : T.Modules) (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) (n : ℕ) :
    IsIso (AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n) := by
  unfold AlgebraicGeometry.Scheme.relativeProj.powTriv
  have h1 := AlgebraicGeometry.Scheme.Modules.isIso_pullbackMonoidalPow V.ι M n
  have : IsIso (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle).hom :=
    ⟨⟨(AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle).inv,
      (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle).hom_inv_id,
      (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle).inv_hom_id⟩⟩
  have h2 := AlgebraicGeometry.Scheme.Modules.isIso_monoidalPowMap
    (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle).hom n
  have h3 := AlgebraicGeometry.Scheme.Modules.isIso_unitPowCollapse V.toScheme n
  exact IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _) (IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3))

/-- **(D-⊗) `monoidalPowCat` becomes multiplication in `Γ(V, O)`.** For sections `u` of `M^{⊗a}` and `v` of `M^{⊗b}`
over `V.ι ''ᵁ A'`: `Λ_{a+b}(monoidalPowCat(u ⊗ v)) = Λ_a(u) · Λ_b(v)`.

**Natural-language proof (complete, as things stand).** `Λ_n = rFIP ≫ pullbackMonoidalPow ≫ monoidalPowMap ẽ ≫
unitPowCollapse`. (i) `rFIP` is compatible with `⊗` on section pairs (`restrictTensorObjIso_hom_app_tensorSections`,
); (ii) `pullbackMonoidalPow` is compatible with `monoidalPowCat`
(`pullbackMonoidalPow_monoidalPowCat`, `ProjectiveBundleUniversalPropertyMonoidalPow.lean`); (iii) `monoidalPowMap` is
compatible with `monoidalPowCat` (`monoidalPowCat_monoidalPowMap`); (iv) on `O^{⊗•}`, `unitPowCollapse` turns
`monoidalPowCat` into the multiplication of `O` — this is the computation inside `liftLocalHomAux_mul`
(`RelativeProjLiftData.lean`, §LiftLocalHomMul: `(unitPowCollapse ⊗ unitPowCollapse) ≫ (λ_ O).hom` and
`(λ_ O).hom` on `tensorSections r s` is `r * s`). Chain (i)–(iv) on `tensorSections u v`, using that the
`tensorHom` of two morphisms acts on `tensorSections` componentwise (`tensorMapHom_app_moduleTensorSection` /
`whiskerRight_app_tensorSections`). ∎


**Edge cases.** `a = 0` or `b = 0`: `monoidalPowCat` is a unitor; `unitPowCollapse 0 = 𝟙`. -/
theorem powTriv_monoidalPowCat (f : T ⟶ X) (M : T.Modules) (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) (a b : ℕ) (A' : V.toScheme.Opens)
    (u : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow M a, V.ι ''ᵁ A'))
    (v : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow M b, V.ι ''ᵁ A')) :
    AlgebraicGeometry.Scheme.Modules.unitSectionsToRing V.toScheme A'
        ((AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle (a + b)).app A'
          ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat M a b).hom.app (V.ι ''ᵁ A')
            (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (V.ι ''ᵁ A') u v))) =
      AlgebraicGeometry.Scheme.Modules.unitSectionsToRing V.toScheme A'
          ((AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle a).app A' u) *
        AlgebraicGeometry.Scheme.Modules.unitSectionsToRing V.toScheme A'
          ((AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle b).app A' v) := by
  have hu := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply V.ι
    (AlgebraicGeometry.Scheme.Modules.monoidalPow M a) A' u
  have hv := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply V.ι
    (AlgebraicGeometry.Scheme.Modules.monoidalPow M b) A' v
  have hw := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply V.ι
    (AlgebraicGeometry.Scheme.Modules.monoidalPow M (a + b)) A'
    ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat M a b).hom.app (V.ι ''ᵁ A')
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (V.ι ''ᵁ A') u v))
  have key := AlgebraicGeometry.Scheme.relativeProj.powTail_app_pullbackSectionsOn_monoidalPowCat V.ι M
    (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle) a b (V.ι ''ᵁ A') A'
    (le_of_eq (V.ι.preimage_image_eq A').symm) u v
  rw [← hu, ← hv, ← hw] at key
  exact key

end PowTriv

namespace LiftData

variable {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules} [M.IsLineBundle]
  (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)

/-! ## The transport isomorphisms on a generalized piece -/

section Transport

/-- `Θ_n : (τ^*O(n))|_V ≅ φ_V^*O_{A(W)}(n)`:
`(τ^*O(n))|_V ≅ (V.ι)^*τ^*O(n) ≅ (V.ι ≫ τ)^*O(n) = (φ_V ≫ ρ)^*O(n) ≅ φ_V^*(ρ^*O(n)) ≅ φ_V^*O_{A(W)}(n)`.
Defined as the variable-level shape `Modules.transportIsoShape` (`…Transport_Shape.lean`) applied to the piece data
(kernel-cheap first-order instances). -/
def twistTransport (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤)
    (hτ : V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
        AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) (n : ℕ) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V.ι ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)) :=
  AlgebraicGeometry.Scheme.Modules.transportIsoShape V.ι (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
    (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)
    (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) hτ
    (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)) (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W (n : ℤ))

/-- `twistTransport` is the transport shape applied to the piece data (one delta step); use it with `rw`
(see `chartTwistIso_eq_shape` for why not `unfold`). -/
theorem twistTransport_eq_shape (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.affineOpens) {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤)
    (hτ : V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
        AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) (n : ℕ) :
    D.twistTransport U e W hle hΦ hτ n =
      AlgebraicGeometry.Scheme.Modules.transportIsoShape V.ι (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
        (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
          (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)
        (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) hτ
        (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)) (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ))
        (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W (n : ℤ)) := rfl

/-- `V.ι ''ᵁ A' ≤ (τ ≫ π)⁻¹ W` for every open `A'` of a generalized piece `V` (`lift_hom`). -/
theorem image_le_preimage (U : T.Opens) (W : X.affineOpens) {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) (A' : V.toScheme.Opens) :
    V.ι ''ᵁ A' ≤
      (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom) ⁻¹ᵁ W.1 := by
  rw [AlgebraicGeometry.Scheme.relativeProj.lift_hom]
  refine le_trans ?_ (hle.trans inf_le_right)
  conv_rhs => rw [← AlgebraicGeometry.Scheme.Opens.opensRange_ι V]
  exact AlgebraicGeometry.Scheme.Hom.image_le_opensRange _ _

/-- `η(x)`: the pullback along `τ ≫ π` of `x ∈ Γ(W, S_n)`, restricted to `V.ι ''ᵁ A'` (`pullbackSectionsOn`). -/
def pulledSection (U : T.Opens) (W : X.affineOpens) {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) (n : ℕ)
    (A' : V.toScheme.Opens) (x : Γ(S.part n, W.1)) :
    Γ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)).obj
        (S.part n), V.ι ''ᵁ A') :=
  AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn
    (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)
    (S.part n) W.1 (V.ι ''ᵁ A') (D.image_le_preimage U W hle A') x

/-- `pullSection 𝒜 Φ hΦ a ha B` is the pulled-back section `pullbackSectionsOn φ O(n) ⊤ B _ (twistSection 𝒜 a ha)`
(definitional: both are the adjunction unit at `⊤` followed by restriction to `B`). -/
theorem _root_.AlgebraicGeometry.Proj.TwistFamily.pullSection_eq_pullbackSectionsOn_top {A : Type u} [CommRing A]
    {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    (Φ : A →+* Γ(Y, ⊤)) (hΦ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map Φ = ⊤) {n : ℕ} (a : A) (ha : a ∈ 𝒜 n)
    (B : Y.Opens) :
    AlgebraicGeometry.Proj.TwistFamily.pullSection 𝒜 Φ hΦ a ha B =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) ⊤ B (AlgebraicGeometry.Proj.TwistFamily.le_preimage_top 𝒜 Φ hΦ B)
        (AlgebraicGeometry.Proj.twistSection 𝒜 a ha) := rfl

/-- `mulHom 𝒜 Φ hΦ a b` is `δ_φ⁻¹ ≫ φ^*(tITO⁻¹ ≫ Proj.twistMul 𝒜 a b ≫ eqToHom)` (one delta step; used with `rw`). -/
theorem _root_.AlgebraicGeometry.Proj.TwistFamily.mulHom_eq_tft {A : Type u} [CommRing A]
    {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    (Φ : A →+* Γ(Y, ⊤)) (hΦ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map Φ = ⊤) (a b : ℕ) :
    AlgebraicGeometry.Proj.TwistFamily.mulHom 𝒜 Φ hΦ a b =
      CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom
          (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
          (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).map
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
              (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).inv ≫
            AlgebraicGeometry.Proj.twistMul 𝒜 (a : ℤ) (b : ℤ) ≫
            CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm)) := rfl

/-! ## The dictionary (named leaves) -/

/-- **(D-α) `α_n` on `η(x)` becomes the pulled-back global section `x/1`.** For `x ∈ Γ(W, S_n)`, `A'` an open of
the generalized piece `V`: `Θ_n(α_n(η x)) = φ_V^*(twistSection (sectionsOf x))|_{A'}`.

**Natural-language proof (complete; Stacks 01MN, 01NR).** Write `τ := lift`, `s := evaluationLocal S n W x`,
`t := twistSection 𝒜 (sectionsOf x)`.
1. `α_n(η x) = (τ^*s)|_{V.ι '' A'}`: `evaluation_comp_app_pullbackSectionsOn` (`…TransportEval.lean`; from
   `pullbackComp_inv_app_pullbackSectionsOn`, `pullback_map_app_pullbackSectionsOn_bc`, `evaluation_app_unit`).
2. `Θ_n = I₁ ≫ I₂ ≫ I₃ ≫ I₄⁻¹ ≫ I₅` (`twistTransport`; `Iso.trans_hom`, `comp_app_apply_tfam`). On `(τ^*s)|_{V.ι '' A'}`:
   `I₁ = rFIP` gives `(V.ι^*(η_τ s))|_{A'}` (`restrictFunctorIsoPullback_hom_app_apply`, `pullbackSectionsOn_res`);
   `I₂ = pullbackComp V.ι τ` gives `((V.ι ≫ τ)^*s)|_{A'}` (`pullbackComp_hom_app_pullbackSectionsOn`);
   `I₃ = pullbackCongr hτ` gives `((φ ≫ ρ)^*s)|_{A'}` (`pullbackCongr_hom_app_pullbackSectionsOn`);
   `I₄⁻¹` gives `(φ^*(η_ρ s))|_{A'}` (`pullbackComp_inv_app_pullbackSectionsOn`);
   `I₅ = φ^*(chartTwistIso)` gives `(φ^*(chartTwistIso(η_ρ s)))|_{A'}` (`pullback_map_app_pullbackSectionsOn_bc`).
3. `chartTwistIso(η_ρ s) = t|_{ρ⁻¹π⁻¹W}` is the leaf `chartTwistIso_hom_app_pullbackSectionsOn_evaluationLocal`;
   moving the restriction (`pullbackSectionsOn_res`) gives `(φ^*t)|_{A'} = pullSection … A'` (definitional). ∎
The opens inequalities `h₀ … h₆` are `image_le_preimage`, `Hom.comp_preimage`, `preimage_image_eq`, `preimage_mono`, `hτ`.

**Formalization.** Step 1 is `evaluation_comp_app_pullbackSectionsOn`; `twistTransport` is
`Modules.transportIsoShape` applied to the piece data, so steps 2–3 are the first-order instance of
`transportIsoShape_hom_app_pullbackSectionsOn` (`…Transport_Shape.lean`) with the chart leaf
`chartTwistIso_hom_app_pullbackSectionsOn_evaluationLocal` as its hypothesis; `pullSection_eq_pullbackSectionsOn_top`
identifies the right-hand side. (A direct rewrite chain on the concrete objects costs about 44 s of kernel time.)

**Edge cases.** `n = 0`: `twistSection` of a degree-0 element, `evaluation S 0` on `S.one`. `A' = ∅`: both sides `0`. -/
theorem twistTransport_evalHom (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤)
    (hτ : V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
        AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) (n : ℕ) (A' : V.toScheme.Opens)
    (x : Γ(S.part n, W.1)) :
    (D.twistTransport U e W hle hΦ hτ n).hom.app A'
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.relativeProj.lift S f M D) (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app (S.part n) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
            (AlgebraicGeometry.Scheme.relativeProj.evaluation S n)).app (V.ι ''ᵁ A') (D.pulledSection U W hle n A' x)) =
      AlgebraicGeometry.Proj.TwistFamily.pullSection (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ
        (S.sectionsOf W.1 n x).1 (S.sectionsOf W.1 n x).2 A' := by
  have h₀ := D.image_le_preimage U W hle A'
  have h₁ : V.ι ''ᵁ A' ≤ AlgebraicGeometry.Scheme.relativeProj.lift S f M D ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact h₀
  have hα := AlgebraicGeometry.Scheme.relativeProj.evaluation_comp_app_pullbackSectionsOn S n W
    (AlgebraicGeometry.Scheme.relativeProj.lift S f M D) (V.ι ''ᵁ A') h₀ h₁ x
  rw [show ((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
        (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app (S.part n) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
        (AlgebraicGeometry.Scheme.relativeProj.evaluation S n)).app (V.ι ''ᵁ A') (D.pulledSection U W hle n A' x) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
        (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)) ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1)
        (V.ι ''ᵁ A') h₁ (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S n W x) from hα,
    AlgebraicGeometry.Proj.TwistFamily.pullSection_eq_pullbackSectionsOn_top]
  rw [D.twistTransport_eq_shape U e W hle hΦ hτ n]
  exact AlgebraicGeometry.Scheme.Modules.transportIsoShape_hom_app_pullbackSectionsOn V.ι
    (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
    (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)
    (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) hτ
    (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)) (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W (n : ℤ))
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1) (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S n W x)
    (AlgebraicGeometry.Proj.twistSection (S.sectionsGrading W.1) (S.sectionsOf W.1 n x).1 (S.sectionsOf W.1 n x).2)
    (fun U' k => AlgebraicGeometry.Scheme.relativeProj.chartTwistIso_hom_app_pullbackSectionsOn_evaluationLocal S W n U' k x)
    A' h₁ _

/-- **(D-β) `β_n` on `η(x)` becomes `Φ_V(x)`.** For `x ∈ Γ(W, S_n)`, `A'` an open of `V`:
`Λ_n(β_n(η x)) = Φ_V(of x)|_{A'}` in `Γ(V, A')`.

**Natural-language proof (complete, as things stand).** `β_n = (pullbackCongr lift_hom).hom ≫ Ψ_n` and
`Λ_n = rFIP ≫ pullbackMonoidalPow ≫ monoidalPowMap ẽ ≫ unitPowCollapse`. By definition
(`liftLocalRingHomAux_of`, `liftLocalPieceAux_apply`), `Φ_V(of x) = (liftLocalHomAux D V.ι ẽ n).app ⊤ (res (η_{V.ι ≫ f} x))`
with `liftLocalHomAux = (pullbackComp V.ι f).inv ≫ V.ι^*Ψ_n ≫ pullbackMonoidalPow ≫ monoidalPowMap ẽ ≫ unitPowCollapse`.
Both sides are therefore the same tail applied to (i) `η_{V.ι}(β_n(η_{τ≫π} x))` read through `rFIP` and (ii)
`(pullbackComp V.ι f).inv (η_{V.ι≫f} x) = η_{V.ι}(η_f x)` (`pullback_comp_inv`), after
`(pullbackCongr lift_hom)(η_{τ≫π} x) = η_f x` (`pullbackCongr_apply`) and naturality of `V.ι^*Ψ_n` on units. Then
restrict from `⊤` to `A'` (naturality of `liftLocalHomAux` and of the units). ∎


**Edge cases.** `n = 0`: `liftLocalPieceAux_zero_apply`. `A' = ∅`: both sides `0`. -/
theorem powTriv_dataHom (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1) (n : ℕ) (A' : V.toScheme.Opens) (x : Γ(S.part n, W.1)) :
    AlgebraicGeometry.Scheme.Modules.unitSectionsToRing V.toScheme A'
        ((AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n).app A'
          (((AlgebraicGeometry.Scheme.Modules.pullbackCongr
            (AlgebraicGeometry.Scheme.relativeProj.lift_hom S f M D)).hom.app (S.part n) ≫ D.Ψ n).app (V.ι ''ᵁ A') (D.pulledSection U W hle n A' x))) =
      V.toScheme.presheaf.map (homOfLE le_top).op
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle
          (DirectSum.of (S.sectionsPiece W.1) n x)) := by
  have hA' : A' ≤ V.ι ⁻¹ᵁ (V.ι ''ᵁ A') := le_of_eq (V.ι.preimage_image_eq A').symm
  have hle'' : V.ι ''ᵁ A' ≤ f ⁻¹ᵁ W.1 := by
    have h0 := AlgebraicGeometry.Scheme.Hom.image_le_opensRange V.ι A'
    rw [AlgebraicGeometry.Scheme.Opens.opensRange_ι] at h0
    exact h0.trans (hle.trans inf_le_right)
  have hA'' : A' ≤ V.ι ⁻¹ᵁ (f ⁻¹ᵁ W.1) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact le_top.trans (AlgebraicGeometry.Scheme.relativeProj.piece_top_le f U W hle)
  -- the right-hand side: `Φ_V(of x)|_{A'} = liftLocalHomAux` on `((V.ι ≫ f)^*x)|_{A'}`, then the tail on `(V.ι^*(Ψ_n(f^*x)))|_{A'}`
  have hR : V.toScheme.presheaf.map (homOfLE le_top).op
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle (DirectSum.of (S.sectionsPiece W.1) n x)) =
      (AlgebraicGeometry.Scheme.relativeProj.powTail V.ι M (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle) n).app A'
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn V.ι
          (AlgebraicGeometry.Scheme.Modules.monoidalPow M n) (f ⁻¹ᵁ W.1) A' hA''
          ((D.Ψ n).app (f ⁻¹ᵁ W.1) (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom f (S.part n) W.1 x))) := by
    have h0 : AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle
        (DirectSum.of (S.sectionsPiece W.1) n x) =
        AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D V.ι
          (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle) W.1
          (AlgebraicGeometry.Scheme.relativeProj.piece_top_le f U W hle) n x :=
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of D V.ι
        (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle) W.1
        (AlgebraicGeometry.Scheme.relativeProj.piece_top_le f U W hle) n x
    rw [h0]
    exact (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_restrict_eq D V.ι _ W.1
      (AlgebraicGeometry.Scheme.relativeProj.piece_top_le f U W hle) n x A').trans
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_app_pullbackSectionsOn D V.ι _ W.1 A' _ hA'' n x)
  rw [hR]
  -- the left-hand side: unit tracking through `pullbackCongr`, `Ψ_n` and `restrictFunctorIsoPullback`
  have h1 := AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_pullbackSectionsOn
    (AlgebraicGeometry.Scheme.relativeProj.lift_hom S f M D) (S.part n) W.1 (V.ι ''ᵁ A')
    (D.image_le_preimage U W hle A') hle'' x
  have h3 : (D.Ψ n).app (V.ι ''ᵁ A')
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn f (S.part n) W.1 (V.ι ''ᵁ A') hle'' x) =
      (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).presheaf.map (homOfLE hle'').op
        ((D.Ψ n).app (f ⁻¹ᵁ W.1) (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom f (S.part n) W.1 x)) :=
    AlgebraicGeometry.Scheme.Modules.app_map (D.Ψ n) hle'' _
  have h2 := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply V.ι
    (AlgebraicGeometry.Scheme.Modules.monoidalPow M n) A'
    ((AlgebraicGeometry.Scheme.Modules.monoidalPow M n).presheaf.map (homOfLE hle'').op
      ((D.Ψ n).app (f ⁻¹ᵁ W.1) (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom f (S.part n) W.1 x)))
  have h4 := AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res V.ι
    (AlgebraicGeometry.Scheme.Modules.monoidalPow M n) hA'' hA' hle''
    ((D.Ψ n).app (f ⁻¹ᵁ W.1) (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom f (S.part n) W.1 x))
  change (AlgebraicGeometry.Scheme.relativeProj.powTail V.ι M
      (AlgebraicGeometry.Scheme.relativeProj.pieceTriv f M U e W hle) n).app A'
    (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι).app
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n)).hom.app A'
      ((D.Ψ n).app (V.ι ''ᵁ A')
        (((AlgebraicGeometry.Scheme.Modules.pullbackCongr
            (AlgebraicGeometry.Scheme.relativeProj.lift_hom S f M D)).app (S.part n)).hom.app (V.ι ''ᵁ A')
          (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn
            (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)
            (S.part n) W.1 (V.ι ''ᵁ A') (D.image_le_preimage U W hle A') x)))) = _
  rw [h1, h3, h2, ← h4]

/-- **(D-μ) the relative twist multiplication becomes the absolute one.** For sections `x` of `τ^*O(a)` and `y` of
`τ^*O(b)` over `V.ι ''ᵁ A'`: `Θ_{a+b}(μ(x ⊗ y)) = μ^{abs}(Θ_a x ⊗ Θ_b y)`.

**Natural-language proof (complete, as things stand; Stacks 01NR, 01MO).**
1. `μ = δ_τ⁻¹ ≫ τ^*(tITO.inv ≫ twistMul S a b ≫ eqToHom)` and `μ^{abs} = δ_φ⁻¹ ≫ φ^*(tITO.inv ≫ Proj.twistMul 𝒜 a b ≫ eqToHom)`.
   `Θ` is `rFIP ≫ pullbackComp ≫ pullbackCongr ≫ pullbackComp⁻¹ ≫ φ^*(chartTwistIso)`; the first four factors are
   the (strong monoidal) comparison isomorphisms of the pseudofunctor `pullback`, compatible with `δ`
   (`pullbackComp_hom_app_pullbackTensorObjHom`;
   `pullbackTensorIsoOpen`/`restrictTensorObjIso` for `rFIP`). So the statement
   reduces to the chart: `ρ^*(tITO.inv ≫ twistMul S a b) ≫ chartTwistIso(a+b) = δ_ρ ≫ (chartTwistIso a ⊗ chartTwistIso b)
   ≫ tITO.inv ≫ Proj.twistMul 𝒜 a b` (as morphisms; then apply `φ^*`, which is strong monoidal).
2. The chart identity: `twistMul S a b` is `glueHom` of the `twistMulLocal S a b W'`, and its restriction to `π⁻¹W` is
   `twistMulLocal S a b W` (`restrictFunctor_map_glueHom`, `TwistPowerIso.lean`). By definition (`TwistMultiplication.lean`)
   `twistMulLocal S a b W = rFIP ≫ pullbackTensorIsoOpen ≫ tITO ≫ (loc a ⊗ loc b) ≫ tITO.inv ≫ (pullbackTensorIsoOpen e)⁻¹
   ≫ e^*(Proj.twistMul 𝒜 a b) ≫ (twistAffineIso S W (a+b)).inv` with `loc n = rFIP⁻¹ ≪≫ twistAffineIso S W n`; pulling
   back along `e.inv` and cancelling `e.inv^* e^* ≅ 𝟙` (`pullbackComp`, `pullbackCongr inv_hom_id`, `pullbackId`, the
   pieces of `chartTwistIso`) gives exactly the required identity — every factor of `chartTwistIso` cancels against
   the corresponding factor of `twistMulLocal`.
3. Finally evaluate on `tensorSections x y`: `δ⁻¹` and the comparison isomorphisms act on section pairs by
   `restrictTensorObjIso_*_app_tensorSections`, `pullbackTensorObjHom_app_unit_tensorSections`, and `tITO.inv` on
   `tensorSections` is `tensorToSheafify_tensorSections`. ∎

**Formalization.** Step 1 is the variable-level `Modules.transportIsoShape_hom_app_mul`
(`…Transport_MulShape.lean`): after `rw [twistTransport_eq_shape]` (three times) and `mulHom_eq_tft`, the statement is
its first-order instance, with the chart identity `chartTwistIso_mul` as hypothesis. Step 2 is `chartTwistIso_mul`:
`twistMul` restricted to `π⁻¹W` is `twistMulLocalShape` (`restrictFunctor_map_twistMul_eq_shape`), and the variable-level
`Modules.chartIsoShape_mul` proves the identity by adjunction-extensionality on pure tensor sections. Step 3 is inside
the two shape lemmas.

**Edge cases.** `a = 0` or `b = 0`: `twistMul` with `O(0) = O`, the unit laws (`twistMulLocal_agree` handles all `a b`). -/
theorem twistTransport_twistMulHom (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤)
    (hτ : V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
        AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) (a b : ℕ) (A' : V.toScheme.Opens)
    (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)), V.ι ''ᵁ A'))
    (y : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)), V.ι ''ᵁ A')) :
    (D.twistTransport U e W hle hΦ hτ (a + b)).hom.app A'
        ((CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
            (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
            ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ))
                (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))).inv ≫
              AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ) ≫
              CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (Nat.cast_add a b).symm))).app (V.ι ''ᵁ A') (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (V.ι ''ᵁ A') x y)) =
      (AlgebraicGeometry.Proj.TwistFamily.mulHom (S.sectionsGrading W.1)
          (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ a b).app A'
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ A'
          ((D.twistTransport U e W hle hΦ hτ a).hom.app A' x) ((D.twistTransport U e W hle hΦ hτ b).hom.app A' y)) := by
  rw [D.twistTransport_eq_shape U e W hle hΦ hτ (a + b), D.twistTransport_eq_shape U e W hle hΦ hτ a,
    D.twistTransport_eq_shape U e W hle hΦ hτ b,
    AlgebraicGeometry.Proj.TwistFamily.mulHom_eq_tft (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ a b]
  exact AlgebraicGeometry.Scheme.Modules.transportIsoShape_hom_app_mul V.ι
    (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
    (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)
    (AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W) hτ
    (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.twist S ((a + b : ℕ) : ℤ))
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (a : ℤ)) (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (b : ℤ))
    (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) ((a + b : ℕ) : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W (a : ℤ)) (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W (b : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso S W ((a + b : ℕ) : ℤ))
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ))
        (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))).inv ≫
      AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (Nat.cast_add a b).symm))
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (a : ℤ))
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (b : ℤ))).inv ≫
      AlgebraicGeometry.Proj.twistMul (S.sectionsGrading W.1) (a : ℤ) (b : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1)) (Nat.cast_add a b).symm))
    (AlgebraicGeometry.Scheme.relativeProj.chartTwistIso_mul S W a b ((a + b : ℕ) : ℤ) (Nat.cast_add a b).symm) A' x y

end Transport

end LiftData

end AlgebraicGeometry.Scheme.relativeProj

end
