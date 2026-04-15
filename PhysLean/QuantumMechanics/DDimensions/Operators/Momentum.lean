/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.QuantumMechanics.DDimensions.Operators.Unbounded
public import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
public import PhysLean.QuantumMechanics.PlanckConstant
public import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Momentum operators

## i. Overview

In this module we introduce several momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `momentumOperator` : (components of) the momentum vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `-iℏ∂ᵢ`.
- `momentumOperatorSqr` : operator acting on Schwartz maps `𝓢(Space d, ℂ)` as `∑ᵢ 𝐩[i]∘𝐩[i]`.
- `momentumUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.

Notation:
- `𝐩[i]` for `momentumOperator i`
- `𝐩²` for `momentumOperatorSqr`

## iii. Table of contents

- A. Momentum vector operator
- B. Momentum-squared operator
- C. Unbounded momentum vector operator

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
noncomputable section
open Constants
open Space
open ContDiff SchwartzMap

variable {d : ℕ} (i : Fin d)

/-!

## A. Momentum vector operator

-/

/-- Component `i` of the momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`. -/
def momentumOperator : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (- Complex.I * ℏ) • (SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ∘L
    (SchwartzMap.fderivCLM ℂ (Space d) ℂ)

@[inherit_doc momentumOperator]
notation "𝐩[" i "]" => momentumOperator i

lemma momentumOperator_apply_fun (ψ : 𝓢(Space d, ℂ)) :
    𝐩[i] ψ = (- Complex.I * ℏ) • ∂[i] ψ := rfl

@[simp]
lemma momentumOperator_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩[i] ψ x = - Complex.I * ℏ * ∂[i] ψ x := rfl

/-!

## B. Momentum-squared operator

-/

/-- The square of the momentum operator, `𝐩² ≔ ∑ᵢ 𝐩ᵢ∘𝐩ᵢ`. -/
def momentumOperatorSqr : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := ∑ i, 𝐩[i] ∘L 𝐩[i]

@[inherit_doc momentumOperatorSqr]
notation "𝐩²" => momentumOperatorSqr

lemma momentumOperatorSqr_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩² ψ x = ∑ i, 𝐩[i] (𝐩[i] ψ) x := by
  dsimp only [momentumOperatorSqr]
  rw [← SchwartzMap.coe_coeHom]
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp', Finset.sum_apply,
    Function.comp_apply, map_sum]

/-!

## C. Unbounded momentum vector operator

-/

open SpaceDHilbertSpace

/-- The momentum operators defined on the Schwartz submodule. -/
def momentumOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ 𝐩[i].toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

@[sorryful]
lemma momentumOperatorSchwartz_isSymmetric : (momentumOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨f, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨f', rfl⟩ := schwartzEquiv.surjective ψ'
  unfold momentumOperatorSchwartz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
    Function.comp_apply, LinearEquiv.symm_apply_apply, schwartzEquiv_inner, momentumOperator_apply,
    neg_mul, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_neg, mul_neg]
  rw [MeasureTheory.integral_neg]
  congr 1
  conv_lhs => rw [show (fun x => Complex.I * ↑↑ℏ * (starRingEnd ℂ) (Space.deriv i (⇑f) x) * f' x) =
    (fun x => Complex.I * ↑ℏ * ((starRingEnd ℂ) (Space.deriv i (⇑f) x) * f' x)) by ext x; ring]
  conv_rhs => rw [show (fun x => (starRingEnd ℂ) (f x) * (Complex.I * ↑↑ℏ * Space.deriv i (⇑f') x)) =
    (fun x => Complex.I * ↑ℏ * ((starRingEnd ℂ) (f x) * Space.deriv i (⇑f') x)) by ext x; ring]
  simp_rw [← smul_eq_mul (a := Complex.I * ↑ℏ)]
  rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul]
  congr 1
  let g := Complex.conjCLE ∘ f
  have hg_diff : Differentiable ℝ g := Complex.conjCLE.differentiable.comp f.differentiable
  have hf'_diff : Differentiable ℝ f' := f'.differentiable
  have hconj_deriv : ∀ x, (starRingEnd ℂ) (Space.deriv i (⇑f) x) = fderiv ℝ g x (Space.basis i) := by
    intro x
    have hf_diffAt : DifferentiableAt ℝ f x := f.differentiableAt
    have hcomp : fderiv ℝ g x = Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x) :=
      Complex.conjCLE.hasFDerivAt.comp x hf_diffAt.hasFDerivAt |>.fderiv
    simp only [g, hcomp, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
      Function.comp_apply, Complex.conjCLE_apply]
    rfl
  simp_rw [hconj_deriv]
  have hderiv_f' : ∀ x, Space.deriv i (⇑f') x = fderiv ℝ f' x (Space.basis i) := fun _ => rfl
  simp_rw [hderiv_f']
  have hg_eq : ∀ x, g x = (starRingEnd ℂ) (f x) := fun _ => rfl
  simp_rw [← hg_eq]
  let hdf : 𝓢(Space d, Space d →L[ℝ] ℂ) := SchwartzMap.fderivCLM ℂ (Space d) ℂ f
  let hdf' : 𝓢(Space d, Space d →L[ℝ] ℂ) := SchwartzMap.fderivCLM ℂ (Space d) ℂ f'
  have hdf_eq : ∀ x, hdf x = fderiv ℝ f x := fun x => SchwartzMap.fderivCLM_apply ℂ f x
  have hdf'_eq : ∀ x, hdf' x = fderiv ℝ f' x := fun x => SchwartzMap.fderivCLM_apply ℂ f' x
  have hg_cont : Continuous g := Complex.continuous_conj.comp f.continuous
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume :=
    hg_cont.aestronglyMeasurable
  have hg_bdd : ∃ C, ∀ x, ‖g x‖ ≤ C := by
    use (SchwartzMap.seminorm ℝ 0 0) f
    intro x
    simp only [g, Function.comp_apply, Complex.conjCLE_apply, Complex.norm_conj]
    exact SchwartzMap.norm_le_seminorm ℝ f x
  have hfg_int : MeasureTheory.Integrable (fun x => g x * f' x) MeasureTheory.volume := by
    obtain ⟨C, hC⟩ := hg_bdd
    exact f'.integrable.bdd_mul hg_aesm (Filter.Eventually.of_forall hC)
  have hfderiv_cont : Continuous (fun x => fderiv ℝ (⇑f) x) := by
    have h1 : Continuous hdf := hdf.continuous
    convert h1 using 1
  have hf'g_cont : Continuous (fun x => fderiv ℝ g x (Space.basis i)) := by
    have h4 : ∀ x, fderiv ℝ g x = Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x) := by
      intro x
      exact Complex.conjCLE.hasFDerivAt.comp x f.differentiableAt.hasFDerivAt |>.fderiv
    have h5 : Continuous (fun x => fderiv ℝ g x) := by
      have hconst_comp : Continuous (fun x => Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) :=
        hfderiv_cont.const_clm_comp Complex.conjCLE.toContinuousLinearMap
      convert hconst_comp using 1
      funext x
      exact h4 x
    exact (ContinuousLinearMap.apply ℝ ℂ (Space.basis i)).continuous.comp h5
  have hf'g_aesm : MeasureTheory.AEStronglyMeasurable (fun x => fderiv ℝ g x (Space.basis i)) MeasureTheory.volume :=
    hf'g_cont.aestronglyMeasurable
  have hf'g_bdd : ∃ C, ∀ x, ‖fderiv ℝ g x (Space.basis i)‖ ≤ C := by
    use ((SchwartzMap.seminorm ℝ 0 0) hdf) * ‖Space.basis i‖
    intro x
    have h4 : fderiv ℝ g x = Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x) :=
      Complex.conjCLE.hasFDerivAt.comp x f.differentiableAt.hasFDerivAt |>.fderiv
    simp only [h4, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
      Function.comp_apply, Complex.conjCLE_apply, Complex.norm_conj]
    calc ‖(fderiv ℝ (⇑f) x) (Space.basis i)‖
        ≤ ‖fderiv ℝ (⇑f) x‖ * ‖Space.basis i‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖hdf x‖ * ‖Space.basis i‖ := by rw [hdf_eq]
      _ ≤ ((SchwartzMap.seminorm ℝ 0 0) hdf) * ‖Space.basis i‖ := by
          gcongr; exact SchwartzMap.norm_le_seminorm ℝ hdf x
  have hf'g_int : MeasureTheory.Integrable (fun x => fderiv ℝ g x (Space.basis i) * f' x) MeasureTheory.volume := by
    obtain ⟨C, hC⟩ := hf'g_bdd
    exact f'.integrable.bdd_mul hf'g_aesm (Filter.Eventually.of_forall hC)
  have hfderiv_f'_cont : Continuous (fun x => fderiv ℝ (⇑f') x) := by
    have h1 : Continuous hdf' := hdf'.continuous
    convert h1 using 1
  have hfg'_cont : Continuous (fun x => fderiv ℝ (⇑f') x (Space.basis i)) := by
    exact (ContinuousLinearMap.apply ℝ ℂ (Space.basis i)).continuous.comp hfderiv_f'_cont
  have hfg'_aesm : MeasureTheory.AEStronglyMeasurable (fun x => g x * fderiv ℝ (⇑f') x (Space.basis i)) MeasureTheory.volume :=
    hg_aesm.mul hfg'_cont.aestronglyMeasurable
  have hg_int : MeasureTheory.Integrable g MeasureTheory.volume := by
    have hf_int : MeasureTheory.Integrable f MeasureTheory.volume := f.integrable
    exact ContinuousLinearMap.integrable_comp Complex.conjCLE.toContinuousLinearMap hf_int
  have hfg'_int : MeasureTheory.Integrable (fun x => g x * fderiv ℝ (⇑f') x (Space.basis i)) MeasureTheory.volume := by
    have hfderiv_f'_bdd : ∃ C, ∀ x, ‖fderiv ℝ (⇑f') x (Space.basis i)‖ ≤ C := by
      use ((SchwartzMap.seminorm ℝ 0 0) hdf') * ‖Space.basis i‖
      intro x
      calc ‖(fderiv ℝ (⇑f') x) (Space.basis i)‖
          ≤ ‖fderiv ℝ (⇑f') x‖ * ‖Space.basis i‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖hdf' x‖ * ‖Space.basis i‖ := by rw [hdf'_eq]
        _ ≤ ((SchwartzMap.seminorm ℝ 0 0) hdf') * ‖Space.basis i‖ := by
            gcongr; exact SchwartzMap.norm_le_seminorm ℝ hdf' x
    obtain ⟨Cf', hCf'⟩ := hfderiv_f'_bdd
    have hfderiv_aesm : MeasureTheory.AEStronglyMeasurable (fun x => fderiv ℝ (⇑f') x (Space.basis i)) MeasureTheory.volume :=
      hfg'_cont.aestronglyMeasurable
    have hmul_comm : (fun x => g x * fderiv ℝ (⇑f') x (Space.basis i)) = (fun x => fderiv ℝ (⇑f') x (Space.basis i) * g x) := by
      ext x; ring
    rw [hmul_comm]
    exact hg_int.bdd_mul hfderiv_aesm (Filter.Eventually.of_forall hCf')
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := Space.basis i) (μ := MeasureTheory.volume)
    hf'g_int hfg'_int hfg_int hg_diff hf'_diff
  rw [key]
  simp only [smul_neg, neg_neg]

/-- The symmetric momentum unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
@[sorryful]
def momentumUnboundedOperator : UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (schwartzSubmodule_dense d) (momentumOperatorSchwartz_isSymmetric i)

end
end QuantumMechanics
