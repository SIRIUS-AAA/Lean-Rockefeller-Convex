/-
Equivalent characterizations of the relative interior of a convex set.

This file uses mathlib's `intrinsicInterior`, which is the interior relative to
the affine span.  All proofs are constructive and contain no `sorry`.
-/

import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Order.DenselyOrdered

open AffineSubspace Set Topology

namespace RelativeInterior

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Line-extension characterization of the relative interior.**

For a convex set `C` in a finite-dimensional real normed space, a point `x`
is in the relative interior precisely when every segment from a point of `C`
to `x` can be extended past `x` without leaving `C`. -/
theorem mem_intrinsicInterior_iff_forall_exists_one_lt
    {C : Set V} (hC : Convex ℝ C) {x : V} :
    x ∈ intrinsicInterior ℝ C ↔
      x ∈ C ∧ ∀ y ∈ C, ∃ t : ℝ, 1 < t ∧ t • x + (1 - t) • y ∈ C := by
  constructor
  · intro hx
    refine ⟨intrinsicInterior_subset hx, ?_⟩
    obtain ⟨xA, hxA, rfl⟩ := mem_intrinsicInterior.mp hx
    let _ : Nonempty (affineSpan ℝ C) := ⟨xA⟩
    intro y hy
    let yA : affineSpan ℝ C := ⟨y, subset_affineSpan ℝ C hy⟩
    have hmem : AffineMap.lineMap (k := ℝ) yA xA (1 : ℝ) ∈
        interior ((↑) ⁻¹' C : Set (affineSpan ℝ C)) := by
      simpa using hxA
    have hnhds : (AffineMap.lineMap (k := ℝ) yA xA : ℝ → affineSpan ℝ C) ⁻¹'
        interior ((↑) ⁻¹' C : Set (affineSpan ℝ C)) ∈ 𝓝 (1 : ℝ) :=
      AffineMap.lineMap_continuous.continuousAt (isOpen_interior.mem_nhds hmem)
    obtain ⟨t, ht, htone⟩ := nonempty_nhds_inter_Ioi hnhds (by simp)
    refine ⟨t, htone, ?_⟩
    have htC := interior_subset ht
    change ((AffineMap.lineMap (k := ℝ) yA xA t : affineSpan ℝ C) : V) ∈ C at htC
    have hcoe : ((AffineMap.lineMap (k := ℝ) yA xA t : affineSpan ℝ C) : V) =
        AffineMap.lineMap y (xA : V) t := by
      exact (affineSpan ℝ C).subtype.apply_lineMap yA xA t
    rw [hcoe] at htC
    simpa [AffineMap.lineMap_apply_module, add_comm] using htC
  · rintro ⟨hxC, hext⟩
    obtain ⟨w, hw⟩ := Set.Nonempty.intrinsicInterior hC ⟨x, hxC⟩
    obtain ⟨t, htone, htC⟩ := hext w (intrinsicInterior_subset hw)
    let z : V := t • x + (1 - t) • w
    have hxsegment : x ∈ openSegment ℝ w z := by
      have hzline : z = AffineMap.lineMap w x t := by
        simp [z, AffineMap.lineMap_apply_module, add_comm]
      rw [hzline]
      have hmem := lineMap_mem_openSegment ℝ w
        (AffineMap.lineMap w x t)
        (show t⁻¹ ∈ Ioo (0 : ℝ) 1 from
          ⟨inv_pos.mpr (zero_lt_one.trans htone), inv_lt_one_of_one_lt₀ htone⟩)
      simpa [ne_of_gt (zero_lt_one.trans htone)] using hmem
    exact hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      hw (subset_intrinsicClosure htC) hxsegment

/-- **Open-segment characterization of the relative interior.**

This is the endpoint-free geometric version of the line-extension theorem:
for every `y ∈ C` distinct from `x`, there is a `z ∈ C` such that `x` lies
strictly between `y` and `z`. -/
theorem mem_intrinsicInterior_iff_forall_exists_openSegment
    {C : Set V} (hC : Convex ℝ C) {x : V} :
    x ∈ intrinsicInterior ℝ C ↔
      x ∈ C ∧ ∀ y ∈ C, y ≠ x → ∃ z ∈ C, x ∈ openSegment ℝ y z := by
  rw [mem_intrinsicInterior_iff_forall_exists_one_lt hC]
  constructor
  · rintro ⟨hxC, hext⟩
    refine ⟨hxC, fun y hy _ ↦ ?_⟩
    obtain ⟨t, htone, htC⟩ := hext y hy
    let z : V := t • x + (1 - t) • y
    refine ⟨z, htC, ?_⟩
    have hzline : z = AffineMap.lineMap y x t := by
      simp [z, AffineMap.lineMap_apply_module, add_comm]
    rw [hzline]
    have hmem := lineMap_mem_openSegment ℝ y
      (AffineMap.lineMap y x t)
      (show t⁻¹ ∈ Ioo (0 : ℝ) 1 from
        ⟨inv_pos.mpr (zero_lt_one.trans htone), inv_lt_one_of_one_lt₀ htone⟩)
    simpa [ne_of_gt (zero_lt_one.trans htone)] using hmem
  · rintro ⟨hxC, hseg⟩
    refine ⟨hxC, fun y hy ↦ ?_⟩
    by_cases hyx : y = x
    · subst y
      exact ⟨2, by norm_num, by simpa using hxC⟩
    obtain ⟨z, hzC, hxsegment⟩ := hseg y hy hyx
    rw [openSegment_eq_image_lineMap] at hxsegment
    obtain ⟨r, hr, hrx⟩ := hxsegment
    refine ⟨r⁻¹, (one_lt_inv₀ hr.1).mpr hr.2, ?_⟩
    have hr0 : r ≠ 0 := ne_of_gt hr.1
    have hzline : z = AffineMap.lineMap y x r⁻¹ := by
      rw [← hrx, AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hr0,
        AffineMap.lineMap_apply_one]
    have hz : r⁻¹ • x + (1 - r⁻¹) • y = z := by
      rw [hzline]
      simp [AffineMap.lineMap_apply_module, add_comm]
    rw [hz]
    exact hzC

end RelativeInterior
