import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan

/-! # A finite type module that is free on a neighbourhood has finite rank

Statement: `X` a scheme, `M` a finite type `O_X`-module (`SheafOfModules.IsFiniteType`), `U ⊆ X` an
open containing a point `x`. If `M|_U ≅ O_U^{(I)}` for some index set `I`, then `I` is finite.

Proof:
1. `M` of finite type ⇒ there are an open neighbourhood `V` of `x`, a finite set `J` and an
   epimorphism `O_V^{⊕J} → M|_V` (definition of `IsFiniteType`: a member of the cover of the
   `LocalGeneratorsData` contains `x`, its `GeneratingSections` has an epimorphism `π` with finite
   index set; `M.over V` and `M|_V` correspond under `Scheme.Modules.overEquiv` — an equivalence,
   preserving epimorphisms and coproducts and sending the unit to the unit — and
   `Scheme.Modules.overFunctorEquiv`).
2. Let `W = U ∩ V ∋ x`. Restriction along the open immersion `W → V` is a left adjoint
   (`Scheme.Modules.restrictAdjunction`), so it preserves epimorphisms and coproducts and sends
   `O_V` to `O_W` (`restrictUnitIso`); this gives an epimorphism `O_W^{⊕J} → (M|_V)|_W`.
3. `(M|_V)|_W ≅ M|_W ≅ (M|_U)|_W` (`restrictFunctorComp`, `restrictFunctorCongr`), and
   `(M|_U)|_W ≅ (O_U^{(I)})|_W ≅ O_W^{(I)}` (restriction ≅ pullback via
   `restrictFunctorIsoPullback`, the hypothesis `e`, and restriction preserves coproducts).
4. Apply the stalk basis lemma for free modules to the scheme `W` and the point `x` (the stalk
   `O_{W,x}` is nonzero, the `I` standard germs in `(O_W^{(I)})_x` are linearly independent, and the
   stalk is finitely generated), so `I` is finite.

References: the definition of finite type in Stacks 01B5; the stalk functor preserves colimits; a
basis of a finitely generated free module over a nonzero ring is finite.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry in
private theorem finite_index_aux {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (I : Type u)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) (V : X.Opens) (hxV : x ∈ V)
    (G : (M.over V).GeneratingSections) [G.IsFiniteType] : Finite I := by
  -- transport to V.toScheme
  let F : SheafOfModules.{u} (X.ringCatSheaf.over V) ⥤ SheafOfModules.{u} V.toScheme.ringCatSheaf :=
    (Scheme.Modules.overEquiv V).functor
  have : F.IsEquivalence := inferInstanceAs (Scheme.Modules.overEquiv V).functor.IsEquivalence
  have : PreservesColimitsOfSize.{u, u} F :=
    F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits.{u, u}
  let e1 : F.obj (M.over V) ≅ (Scheme.Modules.restrictFunctor V.ι).obj M :=
    (Scheme.Modules.overFunctorEquiv V).app M
  let η : SheafOfModules.unit V.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over V)) :=
    (Scheme.Modules.restrictUnitIso V.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv V).app (SheafOfModules.unit X.ringCatSheaf)).symm
  have : Finite G.I := inferInstance
  let MV : SheafOfModules.{u} V.toScheme.ringCatSheaf := (Scheme.Modules.restrictFunctor V.ι).obj M
  let e1' : F.obj (M.over V) ≅ MV := e1
  -- the epimorphism O_V^{⊕J} → M|_V on V
  let πV : SheafOfModules.free (R := V.toScheme.ringCatSheaf) G.I ⟶ MV :=
    (SheafOfModules.mapFreeIso F G.I η).hom ≫ F.map G.π ≫ e1'.hom
  have hπV : Epi πV := by
    have h1 : Epi (F.map G.π) := F.map_epi G.π
    have h2 : Epi (F.map G.π ≫ e1'.hom) := epi_comp _ _
    exact epi_comp _ _
  -- shrink to W = U ⊓ V
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hx, hxV⟩
  let jV : W.toScheme ⟶ V.toScheme := X.homOfLE inf_le_right
  let jU : W.toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  let RV : SheafOfModules.{u} V.toScheme.ringCatSheaf ⥤ SheafOfModules.{u} W.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor jV
  let RU : SheafOfModules.{u} U.toScheme.ringCatSheaf ⥤ SheafOfModules.{u} W.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor jU
  have hRV : PreservesColimitsOfSize.{u, u} RV :=
    (Scheme.Modules.restrictAdjunction jV).leftAdjoint_preservesColimits.{u, u}
  have hRU : PreservesColimitsOfSize.{u, u} RU :=
    (Scheme.Modules.restrictAdjunction jU).leftAdjoint_preservesColimits.{u, u}
  have : PreservesColimitsOfShape (Discrete G.I) RV := hRV.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) RU := hRU.preservesColimitsOfShape
  have : RV.PreservesEpimorphisms := 
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.restrictAdjunction jV)
  let πW : SheafOfModules.free (R := W.toScheme.ringCatSheaf) G.I ⟶ RV.obj MV :=
    (SheafOfModules.mapFreeIso RV G.I (Scheme.Modules.restrictUnitIso jV).symm).hom ≫ RV.map πV
  have hπW : Epi πW := by
    have h1 : Epi (RV.map πV) := RV.map_epi πV
    exact epi_comp _ _
  have hV : jV ≫ V.ι = W.ι := X.homOfLE_ι _
  have hU : jU ≫ U.ι = W.ι := X.homOfLE_ι _
  let ε1 : RV.obj MV ≅ RU.obj ((Scheme.Modules.pullback U.ι).obj M) :=
    ((Scheme.Modules.restrictFunctorComp jV V.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (hV.trans hU.symm)).app M ≪≫
    (Scheme.Modules.restrictFunctorComp jU U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor jU).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)
  let ε : RV.obj MV ≅ SheafOfModules.free (R := W.toScheme.ringCatSheaf) I :=
    ε1 ≪≫ RU.mapIso e ≪≫
    (SheafOfModules.mapFreeIso RU I (Scheme.Modules.restrictUnitIso jU).symm).symm
  exact @MiyaokaMori.FreeStalk.finite_of_epi_of_iso_free W.toScheme ⟨x, hxW⟩ G.I _ (RV.obj MV) πW hπW I ε

theorem AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsFiniteType] (U : X.Opens) (I : Type u)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) :
    Finite I := by
  -- Step 1: finitely many generating sections on a neighbourhood V of x
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M)
  have hcov := σ.coversTop
  rw [Opens.coversTop_iff] at hcov
  have hx' : x ∈ (⨆ i, σ.X i : X.Opens) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  have hfin : (σ.generators i).IsFiniteType := hσ.isFiniteType i
  exact finite_index_aux M U I e x hx (σ.X i) hi (σ.generators i)

end
