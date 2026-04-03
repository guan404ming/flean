# Flean

A Lean 4 formalization of IEEE 754 floating-point arithmetic with mixed-precision analysis, built on Mathlib.

230 theorems, zero `sorry`.

## Getting Started

```
lake build
```

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

## Structure

```
Flean/
├── Core/           Real-valued rounding models, error bounds, double rounding,
│                   cast chain composition, relative error, ULP, Sterbenz
├── Binary/         Bit-level IEEE 754 (BitVec packing, classification, special values)
├── Arith/          Arithmetic operations (add, mul, div, sqrt, FMA, comparisons)
├── Bridge.lean     Refinement connecting bit-level and real-valued models
└── Tactics/        Automation for mixed-precision proofs
```

## Tactics

```lean
-- Prove cast chain exactness (widen-narrow, idempotence, absorption)
example {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary16 (roundNNE binary32 x) = x := by
  flean_cast_safe

-- Derive error bounds for cast chains
example (x : ℝ) :
    |x - roundNNE binary64 x| ≤ |x - roundNNE binary32 x| := by
  flean_cast_bound

-- Quantization scheme error bounds
example {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary32 x = x := by
  flean_quant_bound
```

## Comparison with Flocq

[Flocq](https://flocq.gitlabpages.inria.fr/) (Coq) provides real-valued rounding models. Flean covers similar abstract theory and adds:

- Bit-level IEEE 754 representation with BitVec
- Bit-real refinement bridge
- Compositional cast chain error analysis
- Mixed-precision automation tactics
- Exception flags, comparisons, totalOrder
- Concrete IEEE 754 format instances (binary16/32/64/128)

## License

Apache-2.0
