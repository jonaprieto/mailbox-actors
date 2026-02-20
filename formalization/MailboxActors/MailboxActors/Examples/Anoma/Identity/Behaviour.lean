import MailboxActors.Engine.Behaviour
import MailboxActors.Examples.Anoma.Spec

/-!
# Identity Subsystem — Behaviours

Guards and actions for `identity`, `commitment`, `decryption`,
`verification`, `encryption`, `signDeleg`, `readDeleg`, `nameRegistry`.
-/

namespace MailboxActors.Examples.Anoma.Identity

open MailboxActors

variable (A : AnomaTypes)
private abbrev S (A : AnomaTypes) := anomaEngineSpec A

-- ============================================================================
-- § Identity Behaviour
-- ============================================================================

@[simp] def identityGenerateGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option (A.Backend × Capability) :=
  match @GuardInput.msg (S A) _ inp with
  | .generateReq backend cap => some (backend, cap)
  | _ => none

def identityGenerateAction
    (w : A.Backend × Capability)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityGenerateGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A; Effect.noop

@[simp] def identityDeleteGuard
    (inp : @GuardInput (S A) AnomaIdx.identity) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .deleteReq eid => some eid
  | _ => none

def identityDeleteAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.identity)
    (_ : identityDeleteGuard A inp = some w) :
    @Effect (S A) AnomaIdx.identity :=
  letI := S A; Effect.noop

def identityActions : @Behaviour (S A) AnomaIdx.identity :=
  letI := S A
  [ { Witness := A.Backend × Capability
      guard := identityGenerateGuard A
      action := identityGenerateAction A }
  , { Witness := A.ExternalIdentity
      guard := identityDeleteGuard A
      action := identityDeleteAction A } ]

private theorem identityNonOverlapping :
    @NonOverlappingGuards (S A) _ (identityActions A) := by
  letI := S A; intro inp
  simp only [identityActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def identityBehaviour : @WellFormedBehaviour (S A) AnomaIdx.identity :=
  letI := S A
  { actions := identityActions A
    nonOverlapping := identityNonOverlapping A }

-- ============================================================================
-- § Commitment Behaviour
-- ============================================================================

@[simp] def commitmentSignGuard
    (inp : @GuardInput (S A) AnomaIdx.commitment) :
    Option A.Signable :=
  match @GuardInput.msg (S A) _ inp with
  | .signReq s => some s
  | _ => none

def commitmentSignAction
    (w : A.Signable)
    (inp : @GuardInput (S A) AnomaIdx.commitment)
    (_ : commitmentSignGuard A inp = some w) :
    @Effect (S A) AnomaIdx.commitment :=
  letI := S A; Effect.noop

def commitmentActions : @Behaviour (S A) AnomaIdx.commitment :=
  letI := S A
  [ { Witness := A.Signable
      guard := commitmentSignGuard A
      action := commitmentSignAction A } ]

private theorem commitmentNonOverlapping :
    @NonOverlappingGuards (S A) _ (commitmentActions A) := by
  letI := S A; intro inp
  simp only [commitmentActions, List.filter]
  split <;> simp

def commitmentBehaviour : @WellFormedBehaviour (S A) AnomaIdx.commitment :=
  letI := S A
  { actions := commitmentActions A
    nonOverlapping := commitmentNonOverlapping A }

-- ============================================================================
-- § Decryption Behaviour
-- ============================================================================

@[simp] def decryptionGuard
    (inp : @GuardInput (S A) AnomaIdx.decryption) :
    Option A.Ciphertext :=
  match @GuardInput.msg (S A) _ inp with
  | .decryptReq ct => some ct
  | _ => none

def decryptionAction
    (w : A.Ciphertext)
    (inp : @GuardInput (S A) AnomaIdx.decryption)
    (_ : decryptionGuard A inp = some w) :
    @Effect (S A) AnomaIdx.decryption :=
  letI := S A; Effect.noop

def decryptionActions : @Behaviour (S A) AnomaIdx.decryption :=
  letI := S A
  [ { Witness := A.Ciphertext
      guard := decryptionGuard A
      action := decryptionAction A } ]

private theorem decryptionNonOverlapping :
    @NonOverlappingGuards (S A) _ (decryptionActions A) := by
  letI := S A; intro inp
  simp only [decryptionActions, List.filter]
  split <;> simp

def decryptionBehaviour : @WellFormedBehaviour (S A) AnomaIdx.decryption :=
  letI := S A
  { actions := decryptionActions A
    nonOverlapping := decryptionNonOverlapping A }

-- ============================================================================
-- § Verification Behaviour
-- ============================================================================

@[simp] def verificationGuard
    (inp : @GuardInput (S A) AnomaIdx.verification) :
    Option (A.ExternalIdentity × A.Signable × A.Signature × Bool) :=
  match @GuardInput.msg (S A) _ inp with
  | .verifyReq eid s sig useSF => some (eid, s, sig, useSF)
  | _ => none

def verificationAction
    (w : A.ExternalIdentity × A.Signable × A.Signature × Bool)
    (inp : @GuardInput (S A) AnomaIdx.verification)
    (_ : verificationGuard A inp = some w) :
    @Effect (S A) AnomaIdx.verification :=
  letI := S A; Effect.noop

def verificationActions : @Behaviour (S A) AnomaIdx.verification :=
  letI := S A
  [ { Witness := A.ExternalIdentity × A.Signable × A.Signature × Bool
      guard := verificationGuard A
      action := verificationAction A } ]

private theorem verificationNonOverlapping :
    @NonOverlappingGuards (S A) _ (verificationActions A) := by
  letI := S A; intro inp
  simp only [verificationActions, List.filter]
  split <;> simp

def verificationBehaviour : @WellFormedBehaviour (S A) AnomaIdx.verification :=
  letI := S A
  { actions := verificationActions A
    nonOverlapping := verificationNonOverlapping A }

-- ============================================================================
-- § Encryption Behaviour
-- ============================================================================

@[simp] def encryptionGuard
    (inp : @GuardInput (S A) AnomaIdx.encryption) :
    Option (A.ExternalIdentity × A.Plaintext × Bool) :=
  match @GuardInput.msg (S A) _ inp with
  | .encryptReq eid pt useRF => some (eid, pt, useRF)
  | _ => none

def encryptionAction
    (w : A.ExternalIdentity × A.Plaintext × Bool)
    (inp : @GuardInput (S A) AnomaIdx.encryption)
    (_ : encryptionGuard A inp = some w) :
    @Effect (S A) AnomaIdx.encryption :=
  letI := S A; Effect.noop

def encryptionActions : @Behaviour (S A) AnomaIdx.encryption :=
  letI := S A
  [ { Witness := A.ExternalIdentity × A.Plaintext × Bool
      guard := encryptionGuard A
      action := encryptionAction A } ]

private theorem encryptionNonOverlapping :
    @NonOverlappingGuards (S A) _ (encryptionActions A) := by
  letI := S A; intro inp
  simp only [encryptionActions, List.filter]
  split <;> simp

def encryptionBehaviour : @WellFormedBehaviour (S A) AnomaIdx.encryption :=
  letI := S A
  { actions := encryptionActions A
    nonOverlapping := encryptionNonOverlapping A }

-- ============================================================================
-- § SignDeleg Behaviour
-- ============================================================================

@[simp] def signDelegQueryGuard
    (inp : @GuardInput (S A) AnomaIdx.signDeleg) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .query eid => some eid
  | _ => none

def signDelegQueryAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.signDeleg)
    (_ : signDelegQueryGuard A inp = some w) :
    @Effect (S A) AnomaIdx.signDeleg :=
  letI := S A; Effect.noop

@[simp] def signDelegSubmitGuard
    (inp : @GuardInput (S A) AnomaIdx.signDeleg) :
    Option A.SignEvidence :=
  match @GuardInput.msg (S A) _ inp with
  | .submit ev => some ev
  | _ => none

def signDelegSubmitAction
    (w : A.SignEvidence)
    (inp : @GuardInput (S A) AnomaIdx.signDeleg)
    (_ : signDelegSubmitGuard A inp = some w) :
    @Effect (S A) AnomaIdx.signDeleg :=
  letI := S A; Effect.noop

def signDelegActions : @Behaviour (S A) AnomaIdx.signDeleg :=
  letI := S A
  [ { Witness := A.ExternalIdentity
      guard := signDelegQueryGuard A
      action := signDelegQueryAction A }
  , { Witness := A.SignEvidence
      guard := signDelegSubmitGuard A
      action := signDelegSubmitAction A } ]

private theorem signDelegNonOverlapping :
    @NonOverlappingGuards (S A) _ (signDelegActions A) := by
  letI := S A; intro inp
  simp only [signDelegActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def signDelegBehaviour : @WellFormedBehaviour (S A) AnomaIdx.signDeleg :=
  letI := S A
  { actions := signDelegActions A
    nonOverlapping := signDelegNonOverlapping A }

-- ============================================================================
-- § ReadDeleg Behaviour
-- ============================================================================

@[simp] def readDelegQueryGuard
    (inp : @GuardInput (S A) AnomaIdx.readDeleg) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .query eid => some eid
  | _ => none

def readDelegQueryAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.readDeleg)
    (_ : readDelegQueryGuard A inp = some w) :
    @Effect (S A) AnomaIdx.readDeleg :=
  letI := S A; Effect.noop

@[simp] def readDelegSubmitGuard
    (inp : @GuardInput (S A) AnomaIdx.readDeleg) :
    Option A.ReadEvidence :=
  match @GuardInput.msg (S A) _ inp with
  | .submit ev => some ev
  | _ => none

def readDelegSubmitAction
    (w : A.ReadEvidence)
    (inp : @GuardInput (S A) AnomaIdx.readDeleg)
    (_ : readDelegSubmitGuard A inp = some w) :
    @Effect (S A) AnomaIdx.readDeleg :=
  letI := S A; Effect.noop

def readDelegActions : @Behaviour (S A) AnomaIdx.readDeleg :=
  letI := S A
  [ { Witness := A.ExternalIdentity
      guard := readDelegQueryGuard A
      action := readDelegQueryAction A }
  , { Witness := A.ReadEvidence
      guard := readDelegSubmitGuard A
      action := readDelegSubmitAction A } ]

private theorem readDelegNonOverlapping :
    @NonOverlappingGuards (S A) _ (readDelegActions A) := by
  letI := S A; intro inp
  simp only [readDelegActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def readDelegBehaviour : @WellFormedBehaviour (S A) AnomaIdx.readDeleg :=
  letI := S A
  { actions := readDelegActions A
    nonOverlapping := readDelegNonOverlapping A }

-- ============================================================================
-- § NameRegistry Behaviour
-- ============================================================================

@[simp] def nameRegistryQueryGuard
    (inp : @GuardInput (S A) AnomaIdx.nameRegistry) :
    Option A.ExternalIdentity :=
  match @GuardInput.msg (S A) _ inp with
  | .query eid => some eid
  | _ => none

def nameRegistryQueryAction
    (w : A.ExternalIdentity)
    (inp : @GuardInput (S A) AnomaIdx.nameRegistry)
    (_ : nameRegistryQueryGuard A inp = some w) :
    @Effect (S A) AnomaIdx.nameRegistry :=
  letI := S A; Effect.noop

@[simp] def nameRegistrySubmitGuard
    (inp : @GuardInput (S A) AnomaIdx.nameRegistry) :
    Option A.NameEvidence :=
  match @GuardInput.msg (S A) _ inp with
  | .submit ev => some ev
  | _ => none

def nameRegistrySubmitAction
    (w : A.NameEvidence)
    (inp : @GuardInput (S A) AnomaIdx.nameRegistry)
    (_ : nameRegistrySubmitGuard A inp = some w) :
    @Effect (S A) AnomaIdx.nameRegistry :=
  letI := S A; Effect.noop

def nameRegistryActions : @Behaviour (S A) AnomaIdx.nameRegistry :=
  letI := S A
  [ { Witness := A.ExternalIdentity
      guard := nameRegistryQueryGuard A
      action := nameRegistryQueryAction A }
  , { Witness := A.NameEvidence
      guard := nameRegistrySubmitGuard A
      action := nameRegistrySubmitAction A } ]

private theorem nameRegistryNonOverlapping :
    @NonOverlappingGuards (S A) _ (nameRegistryActions A) := by
  letI := S A; intro inp
  simp only [nameRegistryActions, List.filter]
  cases h : @GuardInput.msg (S A) _ inp <;> simp_all

def nameRegistryBehaviour : @WellFormedBehaviour (S A) AnomaIdx.nameRegistry :=
  letI := S A
  { actions := nameRegistryActions A
    nonOverlapping := nameRegistryNonOverlapping A }

end MailboxActors.Examples.Anoma.Identity
