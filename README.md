# Equivalent Characterizations of the Relative Interior of a Convex Set: A Lean Proof Guide

## 1. Introduction

Let \(V\) be a finite-dimensional real normed vector space, and let \(C\subseteq V\) be a convex set. A point \(x\) is a **relative interior point** of \(C\) if it is a topological interior point of \(C\) when \(C\) is regarded as a subset of its affine hull \(\operatorname{aff}(C)\).

In Lean's mathlib, the relative interior is written as:

```lean
intrinsicInterior ℝ C
```

Together, `intrinsicInterior` and `affineSpan` express the idea of taking the interior relative to the affine hull. The relative interior is often more useful than the ordinary interior when working with lower-dimensional convex sets. For example, a line segment in three-dimensional space has no ordinary interior points, but its non-endpoint points are relative interior points within the affine line containing the segment.

The proof uses the following assumptions:

```lean
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

{C : Set V} (hC : Convex ℝ C) {x : V}
```

Thus, `V` is a finite-dimensional real normed space, `C` is convex, and `x` is the point whose relative-interior membership is being characterized.

## 2. Statement of the Problem

The main theorem is `mem_intrinsicInterior_iff_forall_exists_one_lt`. Its Lean statement is:

```lean
x ∈ intrinsicInterior ℝ C ↔
  x ∈ C ∧ ∀ y ∈ C, ∃ t : ℝ, 1 < t ∧ t • x + (1 - t) • y ∈ C
```

In mathematical notation, this reads:

\[
x\in\operatorname{ri}(C)
\iff
x\in C\ \text{and}\
\forall y\in C,\ \exists t>1,\quad t x+(1-t)y\in C.
\]

This condition has a direct geometric interpretation: the segment joining \(y\) to \(x\) can be extended beyond \(x\), with the extended point still belonging to \(C\).

The file also proves the equivalent open-segment characterization:

```lean
x ∈ intrinsicInterior ℝ C ↔
  x ∈ C ∧ ∀ y ∈ C, y ≠ x → ∃ z ∈ C, x ∈ openSegment ℝ y z
```

In words, for every \(y\in C\) distinct from \(x\), there exists another point \(z\in C\) such that \(x\) lies strictly between \(y\) and \(z\).

## 3. Proof of the Main Theorem

The proof has two directions.

### 3.1 Forward Direction: A Relative Interior Point Allows Segment Extension

Assume:

```lean
hx : x ∈ intrinsicInterior ℝ C
```

The proof proceeds as follows.

1. **Show that \(x\in C\).**  
   This follows from `intrinsicInterior_subset`, since the relative interior of a set is contained in the set itself.

2. **Transfer the problem to the affine hull.**  
   Using `mem_intrinsicInterior`, represent \(x\) by a point `xA` in the affine-span subtype, with:

   ```lean
   hxA : xA ∈ interior ((↑) ⁻¹' C : Set (affineSpan ℝ C))
   ```

   For an arbitrary `y ∈ C`, similarly construct the corresponding point `yA` in the affine hull.

3. **Consider the affine line through `yA` and `xA`.**  
   The line is represented by:

   ```lean
   AffineMap.lineMap yA xA
   ```

   Parameter \(0\) gives `yA`, parameter \(1\) gives `xA`, and a parameter \(t>1\) gives a point on the extension beyond `xA`.

4. **Use continuity to find a parameter greater than \(1\).**  
   Since `xA` lies in the relative interior and the affine line map is continuous, points on the line remain in that interior for parameters sufficiently close to \(1\). The lemma `nonempty_nhds_inter_Ioi` then supplies a parameter `t` strictly greater than \(1\) whose corresponding point still belongs to \(C\).

5. **Return to the original vector space.**  
   The lemma `(affineSpan ℝ C).subtype.apply_lineMap` transports the result from the affine-span subtype back to `V`. Simplification gives:

   ```lean
   t • x + (1 - t) • y ∈ C
   ```

This completes the forward direction.

### 3.2 Reverse Direction: Segment Extension Implies Relative-Interior Membership

Assume that `x ∈ C` and that, for every `y ∈ C`, the segment from `y` to `x` can be extended beyond `x` within `C`.

The proof proceeds as follows.

1. **Choose a point already known to be in the relative interior.**  
   Since `C` is nonempty and convex, and the ambient space is finite-dimensional, use:

   ```lean
   Set.Nonempty.intrinsicInterior hC ⟨x, hxC⟩
   ```

   This provides a point:

   ```lean
   w ∈ intrinsicInterior ℝ C
   ```

2. **Apply the extension hypothesis to `w`.**  
   The hypothesis gives \(t>1\). Define:

   \[
   z=t x+(1-t)w.
   \]

   By the extension assumption, `z ∈ C`.

3. **Show that \(x\) lies strictly between \(w\) and \(z\).**  
   Use the parameter \(t^{-1}\). Since \(t>1\),

   \[
   0<t^{-1}<1.
   \]

   Using `lineMap_mem_openSegment` and the simplification rules for affine line maps, we obtain:

   ```lean
   x ∈ openSegment ℝ w z
   ```

4. **Apply the open-segment property of convex sets.**  
   The point `w` belongs to the relative interior, while `z` belongs to `C` and hence to `intrinsicClosure ℝ C`. Apply:

   ```lean
   hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
   ```

   This shows that the entire open segment `openSegment ℝ w z` is contained in the relative interior. In particular, `x` belongs to the relative interior.

This completes both directions of the main theorem.

## 4. Proof of the Open-Segment Characterization

The second theorem is derived from the first.

- **Forward direction:** The extension condition directly provides the point \(z=t x+(1-t)y\). Since \(0<t^{-1}<1\), the point \(x\) lies in the open segment between `y` and `z`.
- **Reverse direction:** If \(y=x\), choose \(t=2\); the resulting extension point is simply `x`. If \(y\ne x\), the open-segment condition supplies a parameter \(r\in(0,1)\) locating \(x\) on the segment from `y` to `z`. Set \(t=r^{-1}\). Then \(t>1\) and \(z=t x+(1-t)y\), recovering the extension condition in the first theorem.

## 5. Main Ideas Behind the Proof

Instead of explicitly constructing an open ball, the proof relies on three key facts:

1. The relative interior is the topological interior of the set within its affine hull.
2. A continuous affine line map keeps parameters sufficiently close to an interior parameter inside the corresponding open set.
3. An open segment joining a relative-interior point to a point in the relative closure remains entirely within the relative interior.

These facts translate the topological notion of a relative interior point into the geometric statement that every segment ending at that point can be extended beyond it. This is the standard and most commonly used equivalent characterization of the relative interior of a convex set.
