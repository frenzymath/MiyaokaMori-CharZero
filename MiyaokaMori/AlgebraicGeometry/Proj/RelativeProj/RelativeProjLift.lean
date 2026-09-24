import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjFromOfGlobalSectionsCompMap
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftData
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftLocalNaturality
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftMapIrrelevant
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleFrameChange
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleRestriction
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjGlueLemmas
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq

/-! # Morphisms into a relative Proj

The construction of morphisms into the relative Proj of a general graded quasi-coherent algebra (the
construction direction of Stacks 01O4): given `f : T → X`, a line bundle `M` on `T`, and graded maps
`Ψ_m : f^*S_m → M^{⊗m}` preserving unit and multiplication and locally surjective in some positive degree,
one obtains `T → Proj_X S` compatible with the projection to `X`. The special case of a projective bundle
(`projBundle.lift`/`liftLocal`) is an `abbrev` of `lift`/`liftLocal` at the data `liftDataOfEpi`. The two general
gluing lemmas used here live in `RelativeProjGlueLemmas.lean` (namespace `relativeProj`).

Source: Stacks 01O4, 01N8 (morphisms into a relative Proj).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory
/- The input data `relativeProj.LiftData` is defined in `RelativeProjLiftData.lean`. -/


/- The local ring homomorphism (one piece of the lift; the same construction as `projBundle.localRingHom` with
   `Sym^m ψ` replaced by a general `Ψ_m`): `U ⊆ T` open, `e : M|_U ≅ O_U`, `W ⊆ X` open, `V := U ⊓ f⁻¹W`,
   `g := (V ↪ T) ≫ f`. The `m`-th component `Γ(W, S_m) → Γ(V, O)` pulls a section back along `g` and applies
   `g^*S_m ≅ (V→T)^*(f^*S_m) →(Ψ_m) (V→T)^*(M^{⊗m}) → ((V→T)^*M)^{⊗m} →(e^{⊗m}) O^{⊗m} → O`;
   the components assemble into a ring homomorphism on `A(W) = ⊕_m Γ(W, S_m)` (`DirectSum.toSemiring`;
   preservation of `1` and of multiplication follow from `map_one`, `map_mul`). -/

/-! ## The components of `liftLocalRingHom` and its two proof obligations -/

section LiftLocalRingHom

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- The morphism `g = (V ↪ U ↪ T) ≫ f` from `V := U ⊓ f⁻¹W` to `X`. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalBase
    (f : T ⟶ X) (U : T.Opens) (W : X.Opens) : (U ⊓ f ⁻¹ᵁ W).toScheme ⟶ X :=
  (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι) ≫ f

/-- The trivialization `e` pulled back along `V ↪ U`: `(V ↪ T)^*M ≅ O_V`. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv
    (f : T ⟶ X) (M : T.Modules)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)).obj M ≅
      SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U)) U.ι).app M).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback
        (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U))).mapIso
      (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
      (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U))

/-- The module-sheaf map `g^*S_m ⟶ O_V` of the `m`-th component. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalHom
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W)).obj (S.part m) ⟶
      SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp
      (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι) f).inv.app (S.part m) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback
      (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)).map (D.Ψ m) ≫
    AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow
      (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι) M m ≫
    AlgebraicGeometry.Scheme.Modules.monoidalPowMap
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W).hom m ≫
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse _ m

/-- All of `V = U ⊓ f⁻¹W` lies in `g⁻¹W`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le
    (f : T ⟶ X) (U : T.Opens) (W : X.Opens) :
    (⊤ : (U ⊓ f ⁻¹ᵁ W).toScheme.Opens) ≤
      AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W ⁻¹ᵁ W := by
  intro y _
  show f.base ((T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι).base y) ∈ W
  rw [AlgebraicGeometry.Scheme.homOfLE_ι]
  exact y.2.2

/-- Another spelling of `liftLocal_top_le` (with `liftLocalBase` unfolded to `(V ↪ U ↪ T) ≫ f`), for use with the
general form `liftLocalRingHomAux`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le'
    (f : T ⟶ X) (U : T.Opens) (W : X.Opens) :
    (⊤ : (U ⊓ f ⁻¹ᵁ W).toScheme.Opens) ≤ ((T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι) ≫ f) ⁻¹ᵁ W :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W

/-- The section map `Γ(W, S_m) → Γ(V, O)` on the `m`-th graded piece. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (m : ℕ) : S.sectionsPiece W m →+ Γ((U ⊓ f ⁻¹ᵁ W).toScheme, ⊤) :=
  (((AlgebraicGeometry.Scheme.relativeProj.liftLocalHom S f M D U e W m).val.app
      (Opposite.op ⊤)).hom.toAddMonoidHom).comp
    ((((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W)).obj (S.part m)).presheaf.map
        (CategoryTheory.homOfLE
          (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W)).op).hom.comp
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W)).unit.app
          (S.part m)).val.app (Opposite.op W)).hom.toAddMonoidHom)
/-! ### Relation with the general form `liftLocalRingHomAux` (`RelativeProjLiftData.lean`)

`liftLocalHom`, `liftLocalPiece`, `liftLocalRingHom` are the special cases of `liftLocalHomAux`,
`liftLocalPieceAux`, `liftLocalRingHomAux` at `ι := (V ↪ U ↪ T)`, `e' := liftLocalTriv`, definitionally (`rfl`).
The computations in degree `0` and for multiplication (`liftLocalHom_zero`, `liftLocalPiece_zero_apply`,
`liftLocalPiece_one`, `liftLocalHom_mul`, `liftLocalPiece_mul`) are derived from the general form. -/

/-- `liftLocalHom` is the special case of the general form `liftLocalHomAux` (definitionally). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalHom_eq_aux
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (m : ℕ) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalHom S f M D U e W m =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D
        (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W) m := rfl

/-- `liftLocalPiece` is the special case of the general form `liftLocalPieceAux` (definitionally). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_eq_aux
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (m : ℕ) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece S f M D U e W m =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D
        (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W) W
        (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le' f U W) m := rfl

/-- **The degree-`0` module map is the unit isomorphism**: `g^*(S.one) ≫ Φ_0 = (pullbackUnitIso g).hom`
(special case of the general form `liftLocalHomAux_zero`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalHom_zero
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W)).map S.one ≫
        AlgebraicGeometry.Scheme.relativeProj.liftLocalHom S f M D U e W 0 =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W)).hom :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_zero D
    (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W)

/-- Unfolding of the definition of `liftLocalPiece` (`rfl`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_apply
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (m : ℕ) (s : S.sectionsPiece W m) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece S f M D U e W m s =
      ((AlgebraicGeometry.Scheme.relativeProj.liftLocalHom S f M D U e W m).val.app (op ⊤)).hom
        (((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W)).obj _).presheaf.map
          (homOfLE (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W)).op
          ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
            (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W)).unit.app _).val.app (op W)).hom s)) :=
  rfl

/-- **The value of the degree-`0` component on `S.one.app W r` is `g^♯ r`** (restricted to `⊤ ≤ g⁻¹W`; special case
of the general form `liftLocalPieceAux_zero_apply`). Shared by `liftLocalPiece_one` (`r = 1`) and `liftLocal_hom`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_zero_apply
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (r : Γ(X, W)) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece S f M D U e W 0 (S.one.app W r) =
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W).appLE W ⊤
        (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W) r :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_zero_apply D
    (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W) W
    (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W) r

/-- The map assembled from the components preserves `1` (the first hypothesis of `DirectSum.toSemiring`).

Source: Stacks 01O4 / 01N8 (morphisms into a relative Proj are given by graded maps preserving unit and
multiplication). Special case of the general form `liftLocalPieceAux_one`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_one
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece S f M D U e W _
      (GradedMonoid.GOne.one : S.sectionsPiece W 0) = 1 :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_one D
    (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W) W
    (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W)

section LiftLocalHomMul

open CategoryTheory.MonoidalCategory

/-- **Claim M**: `g^*(S.mul m n) ≫ Φ_{m+n} = δ_g ≫ (Φ_m ⊗ Φ_n) ≫ (λ_ O_V).hom` (special case of
`liftLocalHomAux_mul`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalHom_mul
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W)).map (S.mul m n) ≫
        AlgebraicGeometry.Scheme.relativeProj.liftLocalHom S f M D U e W (m + n) =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom
          (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W) (S.part m) (S.part n) ≫
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalHom S f M D U e W m ⊗ₘ
          AlgebraicGeometry.Scheme.relativeProj.liftLocalHom S f M D U e W n) ≫
        (λ_ (𝟙_ (U ⊓ f ⁻¹ᵁ W).toScheme.Modules)).hom :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_mul
    (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι) S f M D
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W) m n

end LiftLocalHomMul

/-- The map assembled from the components preserves multiplication (the second hypothesis of
`DirectSum.toSemiring`).

Source: Stacks 01O4 / 01N8. Special case of the general form `liftLocalPieceAux_mul` (`RelativeProjLiftData.lean`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_mul
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    ∀ {m n : ℕ} (a : S.sectionsPiece W m) (b : S.sectionsPiece W n),
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece S f M D U e W _
          (GradedMonoid.GMul.mul a b) =
        AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece S f M D U e W _ a *
          AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece S f M D U e W _ b :=
  fun a b => AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_mul D
    (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W) W
    (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W) a b

noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    S.sectionsRing W →+* Γ((U ⊓ f ⁻¹ᵁ W).toScheme, ⊤) :=
  DirectSum.toSemiring
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece S f M D U e W)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_one S f M D U e W)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_mul S f M D U e W)

/-- `liftLocalRingHom` is the special case of the general form `liftLocalRingHomAux` (definitionally). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom_eq_aux
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom S f M D U e W =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D
        (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W) W
        (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le' f U W) := rfl

end LiftLocalRingHom

/-- **The image of the irrelevant ideal generates the unit ideal** (the hypothesis of `Proj.fromOfGlobalSections`),
on an **affine** open `V′ ⊆ U ⊓ f⁻¹W`.

Source: Stacks 01O4 (the representability part: if `ψ` is locally surjective in some positive degree, the morphism
to Proj is everywhere defined), 01N8.

## Proof

Let `R = Γ(V′, O)` and `I = Ideal.map (res ∘ liftLocalRingHom) (irrelevant A(W)) ⊆ R`. We show `I = ⊤`.

### (1) At every point `t′ ∈ V′`, the image of some homogeneous element of positive degree is a unit
* `D.generates t′` gives a neighbourhood `U″ ⊆ T` of `t′` and `m > 0` such that
  `Ψ_m|_{U″} : (f^*S_m)|_{U″} → M^{⊗m}|_{U″}` is an epimorphism. Pull back along `V″ := V′ ⊓ U″ ↪ T`:
  `pullbackMonoidalPow` (`pullbackTensorObjHom` is an isomorphism), `monoidalPowMap e′^{⊗m}` and
  `unitPowCollapse` are isomorphisms, so `Φ_m = liftLocalHom … m` restricted to `V″` is an epimorphism, hence
  surjective on stalks `(g^*S_m)_{t′} → O_{V′,t′}`.
* `W` affine and `S_m` quasi-coherent ⟹ `Γ(W, S_m)` generates every stalk of `S_m|_W`; pullback preserves
  "generating the stalk": `(g^*S_m)_{t′} ≅ O_{V′,t′} ⊗_{O_{X,g t′}} (S_m)_{g t′}` is generated by the pullbacks of
  `Γ(W, S_m)`.
* `O_{V′,t′}` is a local ring. The images of finitely many generators under a surjection cannot all lie in the
  maximal ideal (otherwise the submodule they generate is contained in `𝔪`, contradicting surjectivity), so there
  is `r ∈ Γ(W, S_m)` with `liftLocalRingHom(r) = liftLocalPiece m r` a unit at `t′`.
* Put `r` in the `m`-th piece (`DirectSum.of _ m r`); `m > 0`, so `r ∈ irrelevant A(W)`.

### (2) `V′` affine ⟹ an ideal with a unit at every point is `⊤`
If `I ≠ ⊤` then `I ⊆ 𝔪` for some maximal ideal `𝔪` (`Ideal.exists_le_maximal`), corresponding to a point `t′` of
`V′ ≅ Spec R` (`IsAffineOpen.primeIdealOf` / `fromSpec`); no element of `I` is a unit at `t′`, in particular not the
`res (liftLocalRingHom r)` of (1) — contradiction.

### (3) The hypothesis "`V′` affine" cannot be dropped
Counterexample: `T = 𝔸²∖{0}`, `X = Spec k`, `S = k[x₀,x₁]`, `M = O_T`, `Ψ` given by `(x, y)`, `U = T`, `W = X`: the
image of the irrelevant ideal is the ideal `(x, y) ≠ ⊤` of `Γ(T, O) = k[x,y]` (`x`, `y` have no common zero, but
`T` is not affine, so (2) fails). **This is why the definition of `lift` shrinks the local pieces to affine opens.**

## Formalization
Everything is done for the general form `liftLocalRingHomAux D ι e' W hW` (`RelativeProjLiftData.lean`); this
statement is the special case `ι = (V′ ↪ U ⊓ f⁻¹W ↪ U ↪ T)` (`liftLocalRingHom_eq_aux` +
`liftLocalRingHomAux_comp`):
* the general form `liftLocalRingHomAux_map_irrelevant` (`RelativeProjLiftMapIrrelevant.lean`): `Y` affine, `W`
  affine; "epi ⟹ surjective on stalks" and "sections of a quasi-coherent sheaf over an affine open generate the
  stalks" in (1) are given together by `projBundle.exists_mem_basicOpen_of_epi`
  (`ProjectiveBundleUniversalPropertyIrrelevant.lean`); the surjectivity from `generates` lives on `U″ ⊆ T`, is
  first pulled to `V₀ := ι⁻¹U″` (`epi_pullback_map_comp`, a left adjoint preserves epimorphisms), then passes
  through three isomorphisms (`isIso_pullbackMonoidalPow`, `isIso_monoidalPowMap`, `isIso_unitPowCollapse`) to
  give that `Φ_m` is epi on `V₀` (`epi_liftLocalHomAux_of_epi`), and finally `liftLocalPieceAux_comp` pulls the unit
  section on `V₀` back to `Y` (`exists_mem_basicOpen_liftLocalPieceAux`);
* (2) is `projBundle.ideal_eq_top_of_forall_exists_mem_basicOpen`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom_map_irrelevant
    {X T : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1) :
    Ideal.map
        ((T.homOfLE hle).appTop.hom.comp
          (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom S f M D U e W.1))
        (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal = ⊤ := by
  haveI : AlgebraicGeometry.IsAffine V'.toScheme := hV'
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom_eq_aux,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_comp]
  exact AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant D _ _ W _

/- One piece of the lift: on an affine open `V' ⊆ U ⊓ f⁻¹W`, `liftLocalRingHom` restricted to `Γ(V', O)` gives, via
   `Proj.fromOfGlobalSections`, a morphism `V' → Proj A(W)`, which is placed into `Proj_X S` through
   `π⁻¹W ≅ Proj A(W)` (`relativeProj.affineIso`). -/

noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocal {X T : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1) :
    V'.toScheme ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left :=
  AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
      ((T.homOfLE hle).appTop.hom.comp
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom S f M D U e W.1))
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom_map_irrelevant S f M D U e W V' hV' hle) ≫
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv ≫
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι

/-! ## The ingredients of `liftLocal_compat`

The three compatibilities are stated for the general form `liftLocalRingHomAux`
(`RelativeProjLiftLocalNaturality.lean`); here `liftLocal` restricted to an affine open `V₃ ⊆ V′` is rewritten as
"the general form on `V₃.ι`" (`homOfLE_liftLocal`), then `W` is changed (`liftLocalPiece_change_W`), and finally
the trivialization (`AlgebraicGeometry.Proj.ProjectiveTupleFrameChange.fromOfGlobalSections_unit_scale`). -/

section LiftLocalCompat

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- `fromOfGlobalSections` depends only on the ring homomorphism (the irrelevant-ideal condition is a proposition). -/
theorem AlgebraicGeometry.Proj.fromOfGlobalSections_congr_ringHom {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    {φ ψ : A →+* Γ(Y, ⊤)} (h : φ = ψ) (hφ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤)
    (hψ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map ψ = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 φ hφ = AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 ψ hψ := by
  subst h
  rfl

/-- `V ≤ f⁻¹W ⟹ ⊤ ≤ (V.ι ≫ f)⁻¹W`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage (f : T ⟶ X) {V : T.Opens} {W : X.Opens}
    (hV : V ≤ f ⁻¹ᵁ W) : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ f) ⁻¹ᵁ W := by
  intro y _
  show f.base (V.ι.base y) ∈ W
  exact hV y.2

/-- `(V₃ ↪ U ⊓ f⁻¹W) ≫ ((U ⊓ f⁻¹W) ↪ U ↪ T) = V₃.ι`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.homOfLE_comp_liftLocalBase_ι (f : T ⟶ X) (U : T.Opens) (W : X.Opens)
    {V₃ : T.Opens} (h : V₃ ≤ U ⊓ f ⁻¹ᵁ W) :
    T.homOfLE h ≫ (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι) = V₃.ι := by
  rw [← Category.assoc, AlgebraicGeometry.Scheme.homOfLE_homOfLE, AlgebraicGeometry.Scheme.homOfLE_ι]

/-- The trivialization `e : M|_U ≅ O_U` restricted to `V₃ ⊆ U ⊓ f⁻¹W`, as `(pullback V₃.ι).obj M ≅ O_{V₃}`
(`liftLocalTriv` pulled back along `V₃ ↪ U ⊓ f⁻¹W`, then transported along `homOfLE_comp_liftLocalBase_ι`). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalTrivOn (f : T ⟶ X) (M : T.Modules)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    {V₃ : T.Opens} (h : V₃ ≤ U ⊓ f ⁻¹ᵁ W) :
    (AlgebraicGeometry.Scheme.Modules.pullback V₃.ι).obj M ≅ SheafOfModules.unit V₃.toScheme.ringCatSheaf :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
      (AlgebraicGeometry.Scheme.relativeProj.homOfLE_comp_liftLocalBase_ι f U W h)).app M).symm ≪≫
    AlgebraicGeometry.Scheme.Modules.trivComp (T.homOfLE h)
      (T.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι) M
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalTriv f M U e W)

/-- **The ring homomorphism of a piece restricted to `V₃ ⊆ V′`** is the general form
`liftLocalRingHomAux D V₃.ι (liftLocalTrivOn …) W` on `V₃.ι`
(`liftLocalRingHom_eq_aux` + `liftLocalRingHomAux_comp` + `liftLocalRingHomAux_congr`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocal_restrict_ringHom
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (V' : T.Opens) (hle : V' ≤ U ⊓ f ⁻¹ᵁ W) {V₃ : T.Opens} (h₃ : V₃ ≤ V') :
    (T.homOfLE h₃).appTop.hom.comp ((T.homOfLE hle).appTop.hom.comp
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom S f M D U e W)) =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D V₃.ι
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalTrivOn f M U e W (h₃.trans hle)) W
        (AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f ((h₃.trans hle).trans inf_le_right)) := by
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom_eq_aux]
  have hc : (T.homOfLE h₃).appTop.hom.comp (T.homOfLE hle).appTop.hom =
      (T.homOfLE (h₃.trans hle)).appTop.hom := by
    rw [← CommRingCat.hom_comp, ← AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.homOfLE_homOfLE]
  rw [← RingHom.comp_assoc, hc, AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_comp]
  exact (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_congr D
    (AlgebraicGeometry.Scheme.relativeProj.homOfLE_comp_liftLocalBase_ι f U W (h₃.trans hle)) _ W _ _).symm

/-- **A piece restricted to an affine open `V₃ ⊆ V′`**:
`homOfLE ≫ liftLocal = fromOfGlobalSections (Aux D V₃.ι et W) ≫ affineIso⁻¹ ≫ ι`
(`fromOfGlobalSections_naturality` + `liftLocal_restrict_ringHom`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.homOfLE_liftLocal
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1)
    {V₃ : T.Opens} (hV₃ : AlgebraicGeometry.IsAffineOpen V₃) (h₃ : V₃ ≤ V') :
    T.homOfLE h₃ ≫ AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V' hV' hle =
      AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
          (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D V₃.ι
            (AlgebraicGeometry.Scheme.relativeProj.liftLocalTrivOn f M U e W.1 (h₃.trans hle)) W.1
            (AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f
              ((h₃.trans hle).trans inf_le_right)))
          (haveI : AlgebraicGeometry.IsAffine V₃.toScheme := hV₃
           AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant D V₃.ι _ W _) ≫
        (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv ≫
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι := by
  unfold AlgebraicGeometry.Scheme.relativeProj.liftLocal
  rw [← Category.assoc, AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality]
  exact congrArg (fun k => k ≫ (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv ≫
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι)
    (AlgebraicGeometry.Proj.fromOfGlobalSections_congr_ringHom _
      (AlgebraicGeometry.Scheme.relativeProj.liftLocal_restrict_ringHom S f M D U e W.1 V' hle h₃) _ _)

/-- **Change of affine open `W ↝ W₃ ≤ W`** (`V₃` affine, `V₃ ≤ f⁻¹W₃`): the two pieces agree in `Proj_X S`
(`liftLocalRingHomAux_restrict` + `Proj.fromOfGlobalSections_comp_map` + `affineIso_restrict` of Stacks 01NQ). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_change_W
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) {V₃ : T.Opens}
    (hV₃ : AlgebraicGeometry.IsAffineOpen V₃)
    (et : (AlgebraicGeometry.Scheme.Modules.pullback V₃.ι).obj M ≅ SheafOfModules.unit V₃.toScheme.ringCatSheaf)
    (W W₃ : X.affineOpens) (h : W₃.1 ≤ W.1) (hW : (⊤ : V₃.toScheme.Opens) ≤ (V₃.ι ≫ f) ⁻¹ᵁ W.1)
    (hW₃ : (⊤ : V₃.toScheme.Opens) ≤ (V₃.ι ≫ f) ⁻¹ᵁ W₃.1) :
    AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D V₃.ι et W.1 hW)
        (haveI : AlgebraicGeometry.IsAffine V₃.toScheme := hV₃
         AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant D V₃.ι et W hW) ≫
      (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).inv ≫
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι =
    AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W₃.1)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D V₃.ι et W₃.1 hW₃)
        (haveI : AlgebraicGeometry.IsAffine V₃.toScheme := hV₃
         AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant D V₃.ι et W₃ hW₃) ≫
      (AlgebraicGeometry.Scheme.relativeProj.affineIso S W₃).inv ≫
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W₃.1).ι := by
  haveI : AlgebraicGeometry.IsAffine V₃.toScheme := hV₃
  have hφ₃ := AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_map_irrelevant D V₃.ι et W₃ hW₃
  rw [AlgebraicGeometry.Proj.fromOfGlobalSections_congr_ringHom _
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_restrict D V₃.ι et h hW hW₃) _
    (AlgebraicGeometry.Proj.irrelevant_map_comp_eq_top_of_map_eq_top _ _ (S.sectionsRestrict h)
      (S.sectionsRestrict_irrelevant W₃.2 W.2 h) _ hφ₃),
    ← AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map (S.sectionsGrading W.1) (S.sectionsGrading W₃.1)
      (S.sectionsRestrict h) (S.sectionsRestrict_irrelevant W₃.2 W.2 h) _ hφ₃,
    Category.assoc, ← AlgebraicGeometry.Scheme.relativeProj.affineIso_restrict S W₃ W h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, AlgebraicGeometry.Scheme.homOfLE_ι]

/-- **Change of trivialization**: two trivializations `et₁`, `et₂` give the same `fromOfGlobalSections`
(`liftLocalRingHomAux_unit_scale` + `fromOfGlobalSections_unit_scale`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.fromOfGlobalSections_liftLocalRingHomAux_change_triv
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) {Y : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ T)
    (et₁ et₂ : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W)
    (h₁ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι et₁ W hW) = ⊤)
    (h₂ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W)).toIdeal.map
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι et₂ W hW) = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι et₂ W hW) h₂ =
      AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W)
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι et₁ W hW) h₁ := by
  have hu := AlgebraicGeometry.Scheme.Modules.isUnit_unitEndSection_hom (et₁.symm ≪≫ et₂)
  exact AlgebraicGeometry.Proj.ProjectiveTupleFrameChange.fromOfGlobalSections_unit_scale (S.sectionsGrading W)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι et₁ W hW)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι et₂ W hW) hu.unit
    (fun d x hx => by
      rw [hu.unit_spec]
      exact AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_unit_scale D ι et₁ et₂ W hW d x hx) h₁

/-- **Two pieces agree on a common affine open `V₃`** (`V₃ ≤ V₁ ⊓ V₂` affine, `W₃ ≤ W₁ ⊓ W₂` affine, `V₃ ≤ f⁻¹W₃`):
restrict both pieces to `V₃` (`homOfLE_liftLocal`), change both to `W₃` (`liftLocalPiece_change_W`), and finally
change the trivialization. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocal_compat_aux
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U₁ : T.Opens) (e₁ : M.restrict U₁.ι ≅ SheafOfModules.unit U₁.toScheme.ringCatSheaf) (W₁ : X.affineOpens)
    (V₁ : T.Opens) (hV₁ : AlgebraicGeometry.IsAffineOpen V₁) (hle₁ : V₁ ≤ U₁ ⊓ f ⁻¹ᵁ W₁.1)
    (U₂ : T.Opens) (e₂ : M.restrict U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf) (W₂ : X.affineOpens)
    (V₂ : T.Opens) (hV₂ : AlgebraicGeometry.IsAffineOpen V₂) (hle₂ : V₂ ≤ U₂ ⊓ f ⁻¹ᵁ W₂.1)
    {V₃ : T.Opens} (hV₃ : AlgebraicGeometry.IsAffineOpen V₃) (h₃₁ : V₃ ≤ V₁) (h₃₂ : V₃ ≤ V₂)
    (W₃ : X.affineOpens) (hW₃₁ : W₃.1 ≤ W₁.1) (hW₃₂ : W₃.1 ≤ W₂.1) (hV₃W : V₃ ≤ f ⁻¹ᵁ W₃.1) :
    T.homOfLE h₃₁ ≫ AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U₁ e₁ W₁ V₁ hV₁ hle₁ =
      T.homOfLE h₃₂ ≫ AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U₂ e₂ W₂ V₂ hV₂ hle₂ := by
  rw [AlgebraicGeometry.Scheme.relativeProj.homOfLE_liftLocal S f M D U₁ e₁ W₁ V₁ hV₁ hle₁ hV₃ h₃₁,
    AlgebraicGeometry.Scheme.relativeProj.homOfLE_liftLocal S f M D U₂ e₂ W₂ V₂ hV₂ hle₂ hV₃ h₃₂,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_change_W S f M D hV₃ _ W₁ W₃ hW₃₁ _
      (AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f hV₃W),
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_change_W S f M D hV₃ _ W₂ W₃ hW₃₂ _
      (AlgebraicGeometry.Scheme.relativeProj.top_le_ι_comp_preimage f hV₃W)]
  congr 1
  exact (AlgebraicGeometry.Scheme.relativeProj.fromOfGlobalSections_liftLocalRingHomAux_change_triv
    S f M D V₃.ι _ _ W₃.1 _ _ _).symm

end LiftLocalCompat

/-- **Two pieces agree on the overlap** (the compatibility hypothesis of `Cover.glueMorphisms`).

Source: Stacks 01O4 ("up to strict equivalence": a change of trivialization or of affine open only changes the
data by a global unit and does not change the morphism to Proj); 01NQ / 01N8 (the gluing data of the relative Proj).

## Proof

The two local pieces `liftLocal … U₁ e₁ W₁ V₁` and `liftLocal … U₂ e₂ W₂ V₂` agree on `V₁ ×_T V₂` (`= V₁ ⊓ V₂`).
Both are scheme morphisms, so the equality can be checked on an **affine open cover** of `V₁ ⊓ V₂`
(`Scheme.Cover.hom_ext`). Fix such an affine open `V₃ ⊆ V₁ ⊓ V₂` and an affine open neighbourhood
`W₃ ⊆ W₁ ⊓ W₂` of `f(V₃)` (`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`; if necessary shrink `V₃` to an
affine open inside `f⁻¹W₃`).

### (1) Change of trivialization `e₁ ↝ e₂`
On `V₃`, `M` has two trivializations; `e₂ ∘ e₁⁻¹` is an automorphism of `O_{V₃}`, i.e. multiplication by a global
unit `u ∈ Γ(V₃, O)^×`. By definition of `liftLocalHom`, the `m`-th component involves `monoidalPowMap e′.hom m`,
so the `m`-th components of the two `liftLocalRingHom` differ by the factor `u^m`: `Φ²_m = u^m · Φ¹_m`.
`Proj.fromOfGlobalSections` is determined on each `D₊(r)` (`r` homogeneous of degree `d`) by the degree-zero
fractions `a/r^k` (`a` of degree `kd`), and `(u^{kd} a)/(u^{kd} r^k) = a/r^k`, so the powers of `u` cancel and the two
pieces give the same morphism (`AlgebraicGeometry.Proj.ProjectiveTupleFrameChange.fromOfGlobalSections_unit_scale`: two
`fromOfGlobalSections` differing by a graded rescaling by a global unit are equal).

### (2) Change of affine open `W₁ ↝ W₃ ↜ W₂`
`liftLocalRingHom` is compatible with the restriction `A(Wᵢ) → A(W₃)` (`sectionsRestrict`):
`liftLocalPiece … W₃ m ∘ sectionsRestrictPiece = res ∘ liftLocalPiece … Wᵢ m`, because the construction of `Φ_m`
is natural in factorizations of `g` (compatibility of the adjunction unit `η` with composition,
`ModulesPullbackCompMonoidal.unit_comp_app`, plus the restriction maps). `relativeProj.affineIso` (Stacks 01NQ)
is compatible with restriction (`affineIso_inv_ι` and the compatibility of the chart `projChart` with `W₃ ≤ Wᵢ`
in `Stacks01nq.lean`). Hence both sides equal "the piece on `W₃`".

### (3) Combination
On `V₃`, first use (2) to change `W₁`, `W₂` to `W₃`, then (1) to change `e₁` to `e₂`; the two pieces coincide. ∎

## Formalization
* Cover: `isPullback_opens_inf` replaces `pullback V₁.ι V₂.ι` by `V₁ ⊓ V₂`; then the affine open cover `{V₃(p)}` of
  `Cover.mkOfCovers` (`V₃ ⊆ V₁ ⊓ V₂ ⊓ f⁻¹W₃`, `W₃ ⊆ W₁ ⊓ W₂` affine) and `Cover.hom_ext`; each piece is
  `liftLocal_compat_aux`.
* Restriction to `V₃` (`homOfLE_liftLocal`): `AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality`
  (for general `A`, `𝒜`) + the composition compatibility `liftLocalRingHomAux_comp` of the general form
  (`RelativeProjLiftLocalNaturality.lean`) + transport along `homOfLE ≫ homOfLE ≫ U.ι = V₃.ι`
  (`liftLocalRingHomAux_congr`), giving `fromOfGlobalSections (Aux D V₃.ι ẽᵢ Wᵢ) ≫ affineIso⁻¹ ≫ ι`.
* (2) Change of `W` (`liftLocalPiece_change_W`): `liftLocalRingHomAux_restrict` (`Aux` is compatible with
  `sectionsRestrict`) + `Proj.fromOfGlobalSections_comp_map` (`ProjFromOfGlobalSectionsCompMap.lean`:
  `fromOfGlobalSections ℬ φ ≫ Proj.map ρ = fromOfGlobalSections 𝒜 (φ ∘ ρ)`) + `affineIso_restrict` of Stacks 01NQ.
* (1) Change of trivialization (`fromOfGlobalSections_liftLocalRingHomAux_change_triv`):
  `AlgebraicGeometry.Proj.ProjectiveTupleFrameChange.fromOfGlobalSections_unit_scale` (for an arbitrary graded ring `𝒜` and an
  arbitrary scheme); the scaling factor is given by `liftLocalRingHomAux_unit_scale` (`u = (ẽ₁⁻¹ ≫ ẽ₂)(1)`,
  `isUnit_unitEndSection_hom`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocal_compat {X T : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U₁ : T.Opens) (e₁ : M.restrict U₁.ι ≅ SheafOfModules.unit U₁.toScheme.ringCatSheaf) (W₁ : X.affineOpens)
    (V₁ : T.Opens) (hV₁ : AlgebraicGeometry.IsAffineOpen V₁) (hle₁ : V₁ ≤ U₁ ⊓ f ⁻¹ᵁ W₁.1)
    (U₂ : T.Opens) (e₂ : M.restrict U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf) (W₂ : X.affineOpens)
    (V₂ : T.Opens) (hV₂ : AlgebraicGeometry.IsAffineOpen V₂) (hle₂ : V₂ ≤ U₂ ⊓ f ⁻¹ᵁ W₂.1) :
    CategoryTheory.Limits.pullback.fst V₁.ι V₂.ι ≫
        AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U₁ e₁ W₁ V₁ hV₁ hle₁ =
      CategoryTheory.Limits.pullback.snd V₁.ι V₂.ι ≫
        AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U₂ e₂ W₂ V₂ hV₂ hle₂ := by
  have hP := AlgebraicGeometry.isPullback_opens_inf V₁ V₂
  rw [← cancel_epi hP.isoPullback.hom, ← Category.assoc, ← Category.assoc, hP.isoPullback_hom_fst,
    hP.isoPullback_hom_snd]
  -- for each point p ∈ V₁ ⊓ V₂ choose an affine W₃ ∋ f p (W₃ ⊆ W₁ ⊓ W₂) and an affine V₃ ∋ p (V₃ ⊆ V₁ ⊓ V₂ ⊓ f⁻¹W₃)
  have hW₃ : ∀ p : (V₁ ⊓ V₂).toScheme, ∃ W₃ : X.Opens, AlgebraicGeometry.IsAffineOpen W₃ ∧
      f.base p.1 ∈ W₃ ∧ W₃.1 ⊆ (W₁.1 ⊓ W₂.1 : X.Opens).1 := fun p =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset ⟨(hle₁ p.2.1).2, (hle₂ p.2.2).2⟩
  choose W₃ hW₃aff hW₃mem hW₃sub using hW₃
  have hV₃ : ∀ p : (V₁ ⊓ V₂).toScheme, ∃ V₃ : T.Opens, AlgebraicGeometry.IsAffineOpen V₃ ∧
      p.1 ∈ V₃ ∧ V₃.1 ⊆ (V₁ ⊓ V₂ ⊓ f ⁻¹ᵁ W₃ p : T.Opens).1 := fun p =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset ⟨p.2, hW₃mem p⟩
  choose V₃ hV₃aff hV₃mem hV₃sub using hV₃
  have hV₃le : ∀ p, V₃ p ≤ V₁ ⊓ V₂ := fun p => (hV₃sub p).trans inf_le_left
  let 𝒰 : (V₁ ⊓ V₂).toScheme.OpenCover :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers (V₁ ⊓ V₂).toScheme (fun p => (V₃ p).toScheme)
      (fun p => T.homOfLE (hV₃le p)) (fun x => ⟨x, ⟨x.1, hV₃mem x⟩, by
        rw [AlgebraicGeometry.Scheme.homOfLE_apply']
        exact Subtype.ext rfl⟩)
  refine 𝒰.hom_ext _ _ fun p => ?_
  show T.homOfLE (hV₃le p) ≫ T.homOfLE inf_le_left ≫ _ = T.homOfLE (hV₃le p) ≫ T.homOfLE inf_le_right ≫ _
  rw [← Category.assoc, AlgebraicGeometry.Scheme.homOfLE_homOfLE, ← Category.assoc,
    AlgebraicGeometry.Scheme.homOfLE_homOfLE]
  exact AlgebraicGeometry.Scheme.relativeProj.liftLocal_compat_aux S f M D U₁ e₁ W₁ V₁ hV₁ hle₁ U₂ e₂ W₂ V₂ hV₂
    hle₂ (hV₃aff p) _ _ ⟨W₃ p, hW₃aff p⟩ (fun _ hx => (hW₃sub p hx).1) (fun _ hx => (hW₃sub p hx).2)
    ((hV₃sub p).trans inf_le_right)

/-! ## The local pieces are `X`-morphisms (the same argument as `projBundle.liftLocal_hom`) -/

section LiftLocalHom

set_option backward.isDefEq.respectTransparency.types false

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- The value of `liftLocalRingHom` on the structure map `sectionsUnit W r` (placed in the degree-`0` piece) is
`g^♯ r` restricted to `⊤` (`DirectSum.toSemiring_of` + `liftLocalPiece_zero_apply`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom_sectionsUnit
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (r : Γ(X, W)) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom S f M D U e W ((S.sectionsUnit W r).1) =
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W).appLE W ⊤
        (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W) r := by
  show DirectSum.toSemiring _ _ _ (DirectSum.of (S.sectionsPiece W) 0 (S.one.app W r)) = _
  exact (DirectSum.toSemiring_of _ _ _ 0 _).trans
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPiece_zero_apply S f M D U e W r)

/-- **The local piece is an `X`-morphism**: `liftLocal … V' … ≫ π = V'.ι ≫ f`.
Route: `relativeProj.affineIso_inv_ι_hom` (`RelativeProjGlueLemmas.lean`) turns `liftLocal ≫ π` into
`fromOfGlobalSections ≫ toSpecZero ≫ Spec(unitZero) ≫ isoSpec⁻¹ ≫ W.ι`; Mathlib's
`fromOfGlobalSections_toSpecZero` turns this into `V'.toSpecΓ ≫ Spec.map(Φ ∘ algebraMap) ≫ …`; on the right,
`V'.ι ≫ f = f.resLE W V' ≫ W.ι` and `f.resLE ≫ W.toSpecΓ = V'.toSpecΓ ≫ Spec.map (f.appLE W V')`
(`Scheme.Opens.toSpecΓ_SpecMap_appLE`). The remaining ring-map identity
`Φ ∘ algebraMap ∘ unitZero = topIso⁻¹ ∘ f.appLE W V'` is `liftLocalRingHom_sectionsUnit` (in degree `0`, `Φ` is
`g^♯`); then the composite of `g^♯` with `(homOfLE hle)^♯` is expanded by
`Scheme.Hom.comp_app`/`homOfLE_app`/`Opens.ι_app` into `f.app W ≫ T.presheaf.map _`, and morphisms in `Opens` are
unique, so `rfl`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocal_hom
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V' hV' hle ≫
        (AlgebraicGeometry.Scheme.relativeProj S).hom = V'.ι ≫ f := by
  have hle' : V' ≤ f ⁻¹ᵁ W.1 := hle.trans inf_le_right
  dsimp only [AlgebraicGeometry.Scheme.relativeProj.liftLocal]
  rw [Category.assoc, Category.assoc, AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι_hom,
    AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero_assoc]
  have hR : f.resLE W.1 V' hle' = V'.toScheme.toSpecΓ ≫ Spec.map V'.topIso.inv ≫
      Spec.map (f.appLE W.1 V' hle') ≫ W.2.isoSpec.inv := by
    rw [← Category.assoc, ← Category.assoc]
    change _ = (V'.toSpecΓ ≫ Spec.map (f.appLE W.1 V' hle')) ≫ W.2.isoSpec.inv
    rw [AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc,
      AlgebraicGeometry.IsAffineOpen.toSpecΓ_isoSpec_inv, Category.comp_id]
  rw [← AlgebraicGeometry.Scheme.Hom.resLE_comp_ι f hle', hR]
  simp only [Category.assoc]
  rw [← AlgebraicGeometry.Spec.map_comp_assoc, ← AlgebraicGeometry.Spec.map_comp_assoc]
  have hmor : (AlgebraicGeometry.Scheme.relativeProj.liftLocalBase f U W.1).appLE W.1 ⊤
        (AlgebraicGeometry.Scheme.relativeProj.liftLocal_top_le f U W.1) ≫
      (T.homOfLE hle).appTop = f.appLE W.1 V' hle' ≫ V'.topIso.inv := by
    unfold AlgebraicGeometry.Scheme.relativeProj.liftLocalBase
    simp only [AlgebraicGeometry.Scheme.Hom.appTop, AlgebraicGeometry.Scheme.Hom.appLE,
      AlgebraicGeometry.Scheme.Hom.comp_app, AlgebraicGeometry.Scheme.homOfLE_app,
      AlgebraicGeometry.Scheme.Opens.ι_app, AlgebraicGeometry.Scheme.Opens.topIso_inv,
      AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_map, Category.assoc]
    erw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  have key : CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero ⟨W.1, W.2⟩) ≫
      CommRingCat.ofHom (((T.homOfLE hle).appTop.hom.comp
          (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom S f M D U e W.1)).comp
        (algebraMap (S.sectionsGrading W.1 0) (S.sectionsRing W.1))) =
      f.appLE W.1 V' hle' ≫ V'.topIso.inv := by
    ext r
    show (T.homOfLE hle).appTop (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom S f M D U e W.1
      ((S.sectionsUnit W.1 r).1)) = _
    rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHom_sectionsUnit]
    exact congrArg (fun k => k.hom r) hmor
  exact congrArg (fun k => V'.toScheme.toSpecΓ ≫ Spec.map k ≫ W.2.isoSpec.inv ≫ W.1.ι) key

end LiftLocalHom

/- The morphism `T → Proj_X S`: for every point `t` of `T` choose a trivializing open `U_t ∋ t` of `M` (local
   triviality of `IsLineBundle`, a class field, chosen by its property) and an affine open `W_t ∋ f(t)`, then an
   **affine** open `V_t ∋ t` with `V_t ⊆ U_t ⊓ f⁻¹W_t`; take `liftLocal` on `V_t` and glue along the open cover
   `{V_t}`. The pieces must be shrunk to affine opens: the hypothesis "image of the irrelevant ideal = ⊤" of
   `Proj.fromOfGlobalSections` is false on `U_t ⊓ f⁻¹W_t` when that open is not affine (counterexample in the
   docstring of `liftLocalRingHom_map_irrelevant`: `T = 𝔸²∖{0} → ℙ¹`), even for legitimate data in the sense of
   Stacks 01O4. The two proof obligations are the theorems `liftLocalRingHom_map_irrelevant` and `liftLocal_compat`. -/

noncomputable def AlgebraicGeometry.Scheme.relativeProj.lift {X T : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) :
    T ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left :=
  let hU := fun t : T => SheafOfModules.IsLineBundle.locally_trivial (M := M) t
  let U : T → T.Opens := fun t => (hU t).choose
  let e : ∀ t, M.restrict (U t).ι ≅ SheafOfModules.unit (U t).toScheme.ringCatSheaf :=
    fun t => (hU t).choose_spec.snd.some
  let hW := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := f.base t) (U := ⊤) trivial
  let W : T → X.affineOpens := fun t => ⟨(hW t).choose, (hW t).choose_spec.1⟩
  let hA := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t) (U := U t ⊓ f ⁻¹ᵁ (W t).1)
      ⟨(hU t).choose_spec.fst, (hW t).choose_spec.2.1⟩
  let Vt : T → T.Opens := fun t => (hA t).choose
  have hVt : ∀ t, AlgebraicGeometry.IsAffineOpen (Vt t) := fun t => (hA t).choose_spec.1
  have hle : ∀ t, Vt t ≤ U t ⊓ f ⁻¹ᵁ (W t).1 := fun t => (hA t).choose_spec.2.2
  have hcov : TopologicalSpace.IsOpenCover Vt := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, (hA t).choose_spec.2.1⟩
  (T.openCoverOfIsOpenCover Vt hcov).glueMorphisms
    (fun t => AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D (U t) (e t) (W t) (Vt t) (hVt t) (hle t))
    (fun s t => AlgebraicGeometry.Scheme.relativeProj.liftLocal_compat S f M D
      (U s) (e s) (W s) (Vt s) (hVt s) (hle s) (U t) (e t) (W t) (Vt t) (hVt t) (hle t))

/-- **`lift` is an `X`-morphism**: `lift ≫ π = f` (Stacks 01O4: `F_1` is a functor on `X`-schemes).
`glueMorphisms_comp_eq_of_forall` (`RelativeProjGlueLemmas.lean`) reduces to each piece of the cover `{V_t}`, then
`liftLocal_hom`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.lift_hom {X T : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) :
    AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom = f := by
  dsimp only [AlgebraicGeometry.Scheme.relativeProj.lift]
  refine AlgebraicGeometry.Scheme.relativeProj.glueMorphisms_comp_eq_of_forall _ _ _ _ _ (fun t => ?_)
  exact AlgebraicGeometry.Scheme.relativeProj.liftLocal_hom S f M D _ _ _ _ _ _

end
