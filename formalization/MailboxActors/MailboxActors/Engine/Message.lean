import MailboxActors.Basic

/-!
# Messages
-/

namespace MailboxActors

variable [EngineSpec]

/-- The total message type collects all message payloads across engine types:
    `TotalMsg ≡ Σ (i : 𝕀). Msg_i`. -/
def TotalMsg := (i : EngineSpec.EngIdx) × EngineSpec.MsgType i

/-- A message packet in transit. -/
structure Message where
  sender : Address
  target : Address
  payload : TotalMsg

/-- The `Append` wrapper for mailbox engine messages: `Msg_m = Append(Msg_i)`. -/
inductive Append (α : Type) where
  | mk : α → Append α

end MailboxActors
