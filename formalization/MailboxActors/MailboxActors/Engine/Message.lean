/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Authors: Jonathan Prieto-Cubides
-/
import MailboxActors.Basic

/-!
# Messages

Paper Definitions 3–5.
-/

namespace MailboxActors

variable [EngineSpec]

/-- The total message type collects all message payloads across engine types.
    Paper equation (3): `TotalMsg ≡ Σ (i : 𝕀). Msg_i`. -/
def TotalMsg := (i : EngineSpec.EngIdx) × EngineSpec.MsgType i

/-- A message packet in transit.  Paper Definition 4. -/
structure Message where
  sender : Address
  target : Address
  payload : TotalMsg

/-- The `Append` wrapper for mailbox engine messages.
    Paper Definition 18: `Msg_m = Append(Msg_i)`. -/
inductive Append (α : Type) where
  | mk : α → Append α

end MailboxActors
