# Flean

A Lean 4 formalization of IEEE 754 floating-point arithmetic, built on Mathlib.

## Structure

- **Core** -- Real-valued rounding models (formats, rounding modes, error bounds, ULP, double rounding)
- **Binary** -- Bit-level IEEE 754 representation (BitVec packing, classification, special values)
- **Arith** -- Arithmetic operations (add, mul, div, sqrt, FMA, comparisons, conversions)
- **Bridge** -- Refinement connecting bit-level and real-valued models
- **Tactics** -- Mixed-precision automation for ML compiler analysis

## Key Results

| Result | File |
|---|---|
| Rounding modes (all 5 IEEE 754) | `Core/Rounding.lean` |
| Monotonicity and idempotence | `Core/RoundProps.lean`, `Core/DirectedRound.lean` |
| Relative error bounds | `Core/RelativeError.lean` |
| ULP and Sterbenz lemma | `Core/ULP.lean` |
| Double rounding (directed + NNE) | `Core/DoubleRound.lean`, `Core/DoubleRoundNNE.lean` |
| Cast chain composition | `Core/CastChain.lean` |
| Round-round ordering | `Core/RoundRound.lean` |
| FLX / FLT / FTZ models | `Core/Models.lean` |
| Bit-real refinement | `Bridge.lean` |
| Exception flags | `Arith/Exceptions.lean` |
| Mixed-precision casts | `Arith/Conversions.lean` |

217 theorems/lemmas, all without sorry.

## Build

```
lake build
```

Requires Lean 4 and Mathlib.

## Comparison with Flocq

Flocq (Coq) provides real-valued rounding models. Flean covers similar abstract theory and adds bit-level operations, exception flags, comparisons, mixed-precision casts, and an ML-oriented tactic, bridging the gap between pure math and IEEE 754's operational spec.
