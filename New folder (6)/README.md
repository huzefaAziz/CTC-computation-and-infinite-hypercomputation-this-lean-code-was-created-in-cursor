# Closed Timelike Curves from Regular Matter

This Lean 4 formalization explores the relationship between Closed Timelike Curves (CTCs) and regular matter in general relativity.

## Overview

Closed Timelike Curves are paths in spacetime that loop back on themselves, potentially allowing time travel. A fundamental question in physics is whether such curves can be created using regular matter that obeys standard energy conditions.

## Key Concepts

### Spacetime Structure
- **SpacetimePoint**: A point in 4-dimensional spacetime (3 space + 1 time)
- **Vector**: A vector in the tangent space at a point
- **LorentzianMetric**: The metric tensor with signature (-+++), which defines distances and causality
- **Spacetime**: A spacetime manifold equipped with a Lorentzian metric

### Curves
- **TimelikeCurve**: A curve where the tangent vector is always timelike (inside the light cone)
- **ClosedTimelikeCurve (CTC)**: A timelike curve that closes on itself, allowing a particle to return to its starting point in spacetime

### Matter and Energy
- **StressEnergyTensor**: Describes the matter and energy distribution in spacetime
- **Energy Conditions**: Physical constraints that regular matter must satisfy:
  - **Weak Energy Condition (WEC)**: Energy density is non-negative
  - **Null Energy Condition (NEC)**: Energy density along light rays is non-negative
  - **Dominant Energy Condition (DEC)**: Energy flows causally (no faster than light)
  - **Strong Energy Condition (SEC)**: Gravity is always attractive

### Regular Matter
- **RegularMatter**: Matter that satisfies WEC, NEC, and DEC

## Main Results

1. **no_ctc_from_regular_matter**: If spacetime is initially free of CTCs and contains only regular matter, CTCs cannot develop.

2. **ctc_requires_exotic_matter**: If a CTC exists, the stress-energy tensor must violate at least one energy condition, meaning exotic matter is required.

3. **ChronologyProtectionConjecture**: Hawking's conjecture that the laws of physics prevent the formation of CTCs from regular matter.

## Physics Context

This formalization relates to the **Chronology Protection Conjecture** proposed by Stephen Hawking, which states that the laws of physics prevent the formation of closed timelike curves. The key insight is that creating a CTC would require exotic matter that violates standard energy conditions, which regular matter (like normal matter, electromagnetic fields, etc.) cannot provide.

## Usage

To use this code, you'll need Lean 4 installed. The code can be loaded and explored in a Lean environment to understand the formal relationships between CTCs, energy conditions, and regular matter.

