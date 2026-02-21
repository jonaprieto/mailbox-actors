import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Identity Management Engine — Behaviour

## Generate Request

When `generateReq` arrives with a backend and capability, the identity
management engine:
1. Increments `nextId` to reserve an identity slot.
2. Spawns commitment and/or decryption sub-engines based on the
   requested capability:
   - `commit` → spawns a commitment engine.
   - `decrypt` → spawns a decryption engine.
   - `both` → spawns both.

## Delete Request

When `deleteReq` arrives, the engine acknowledges the deletion request.
The actual teardown of sub-engines is left abstract.

## Crypto Results

When `signResult`, `decryptResult`, `verifyResult`, or `encryptResult`
arrive from sub-engines, the identity manager receives the crypto
computation result. Forwarding to the original requester is left
abstract because the requester's engine type is not known statically.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Identity Management Behaviour
-- ============================================================================

/-- Guard for `generateReq` messages. -/
@[simp] def identityGenerateGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option (A.Backend × Capability) :=
  match @GuardInput.msg (S A) _ inp with
  | .generateReq backend cap => some (backend, cap)
  | _ => none

/-- Action for `generateReq`: increment `nextId` and spawn
    commitment/decryption sub-engines based on the capability.

    - `commit` → `Effect.chain update (spawn commitment)`
    - `decrypt` → `Effect.chain update (spawn decryption)`
    - `both` → `Effect.chain update (chain (spawn commitment) (spawn decryption))` -/
def identityGenerateAction
    (w : A.Backend × Capability)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityGenerateGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A
  let env := inp.env
  let st := env.localState
  let backend := w.1
  let cap := w.2
  let env' := { env with localState := { st with nextId := st.nextId + 1 } }
  match cap with
  | .commit =>
    Effect.chain
      (Effect.update env')
      (Effect.spawn AnomaIdx.commitment
        ({ backend := backend } : CommitmentCfg A) ())
  | .decrypt =>
    Effect.chain
      (Effect.update env')
      (Effect.spawn AnomaIdx.decryption
        ({ backend := backend } : DecryptionCfg A) ())
  | .both =>
    Effect.chain
      (Effect.update env')
      (Effect.chain
        (Effect.spawn AnomaIdx.commitment
          ({ backend := backend } : CommitmentCfg A) ())
        (Effect.spawn AnomaIdx.decryption
          ({ backend := backend } : DecryptionCfg A) ()))

/-- Guard for `deleteReq` messages. -/
@[simp] def identityDeleteGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .deleteReq eid => some eid
  | _ => none

/-- Action for `deleteReq`: noop. In a full implementation this
    would terminate the commitment/decryption sub-engines associated
    with the deleted identity. -/
def identityDeleteAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityDeleteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A; Effect.noop

/-- Guard for `signResult` messages from commitment sub-engines. -/
@[simp] def identitySignResultGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option A.Signature :=
  match @GuardInput.msg (S A) _ inp with
  | .signResult sig => some sig
  | _ => none

/-- Action for `signResult`: the identity manager receives the
    signature. Forwarding to the original requester is left abstract. -/
def identitySignResultAction
    (w : A.Signature)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identitySignResultGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A; Effect.noop

/-- Guard for `decryptResult` messages from decryption sub-engines. -/
@[simp] def identityDecryptResultGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option A.Plaintext :=
  match @GuardInput.msg (S A) _ inp with
  | .decryptResult pt => some pt
  | _ => none

/-- Action for `decryptResult`: the identity manager receives the
    plaintext. Forwarding to the original requester is left abstract. -/
def identityDecryptResultAction
    (w : A.Plaintext)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityDecryptResultGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A; Effect.noop

/-- Guard for `verifyResult` messages from verification sub-engines. -/
@[simp] def identityVerifyResultGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option Bool :=
  match @GuardInput.msg (S A) _ inp with
  | .verifyResult b => some b
  | _ => none

/-- Action for `verifyResult`: the identity manager receives the
    verification result. Forwarding to the original requester is left
    abstract. -/
def identityVerifyResultAction
    (w : Bool)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityVerifyResultGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A; Effect.noop

/-- Guard for `encryptResult` messages from encryption sub-engines. -/
@[simp] def identityEncryptResultGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option A.Ciphertext :=
  match @GuardInput.msg (S A) _ inp with
  | .encryptResult ct => some ct
  | _ => none

/-- Action for `encryptResult`: the identity manager receives the
    ciphertext. Forwarding to the original requester is left abstract. -/
def identityEncryptResultAction
    (w : A.Ciphertext)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityEncryptResultGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A; Effect.noop

def identityActions : @Behaviour (S A) AnomaIdx.identity :=
  letI := S A
  [ { Witness := A.Backend × Capability
      guard := identityGenerateGuard A
      action := identityGenerateAction A }
  , { Witness := A.ExternalIdentity
      guard := identityDeleteGuard A
      action := identityDeleteAction A }
  , { Witness := A.Signature
      guard := identitySignResultGuard A
      action := identitySignResultAction A }
  , { Witness := A.Plaintext
      guard := identityDecryptResultGuard A
      action := identityDecryptResultAction A }
  , { Witness := Bool
      guard := identityVerifyResultGuard A
      action := identityVerifyResultAction A }
  , { Witness := A.Ciphertext
      guard := identityEncryptResultGuard A
      action := identityEncryptResultAction A } ]

private theorem identityNonOverlapping :
    @NonOverlappingGuards (S A) _ (identityActions A) := by
  letI := S A; intro inp
  simp only [identityActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def identityBehaviour : @WellFormedBehaviour (S A) AnomaIdx.identity :=
  letI := S A
  { actions := identityActions A
    nonOverlapping := identityNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
