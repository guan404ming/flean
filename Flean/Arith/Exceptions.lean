import Flean.Core.Format

/-!
# Flean.Arith.Exceptions

IEEE 754 exception flags: Invalid Operation, Division by Zero,
Overflow, Underflow, Inexact.
-/

namespace Flean

/-- IEEE 754 exception flag types. -/
inductive ExceptionFlag where
  | invalidOperation
  | divisionByZero
  | overflow
  | underflow
  | inexact
  deriving DecidableEq, Repr

/-- A set of raised exception flags, represented as a record of booleans. -/
structure ExceptionFlags where
  invalidOperation : Bool := false
  divisionByZero : Bool := false
  overflow : Bool := false
  underflow : Bool := false
  inexact : Bool := false
  deriving DecidableEq, Repr

/-- No exceptions raised. -/
def ExceptionFlags.none : ExceptionFlags := {}

/-- Merge two exception flag sets (logical OR). -/
def ExceptionFlags.merge (a b : ExceptionFlags) : ExceptionFlags where
  invalidOperation := a.invalidOperation || b.invalidOperation
  divisionByZero := a.divisionByZero || b.divisionByZero
  overflow := a.overflow || b.overflow
  underflow := a.underflow || b.underflow
  inexact := a.inexact || b.inexact

instance : Append ExceptionFlags where
  append := ExceptionFlags.merge

/-- Check if any exception is raised. -/
def ExceptionFlags.any (flags : ExceptionFlags) : Bool :=
  flags.invalidOperation || flags.divisionByZero || flags.overflow ||
  flags.underflow || flags.inexact

/-- The result of a floating-point operation: a value paired with exception flags. -/
structure OpResult (α : Type) where
  value : α
  flags : ExceptionFlags := {}
  deriving Repr

/-- Map over the value of an OpResult. -/
def OpResult.map {α β : Type} (f : α → β) (r : OpResult α) : OpResult β where
  value := f r.value
  flags := r.flags

/-- Chain two operations, merging exception flags. -/
def OpResult.bind {α β : Type} (r : OpResult α) (f : α → OpResult β) : OpResult β :=
  let r' := f r.value
  { value := r'.value, flags := r.flags ++ r'.flags }

end Flean
