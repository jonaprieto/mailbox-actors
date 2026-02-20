import MailboxActors.Examples.Anoma.EngIdx

/-!
# Identity Subsystem — Message, Config, and State Types

Engines: `identity`, `commitment`, `decryption`, `verification`,
`encryption`, `signDeleg`, `readDeleg`, `nameRegistry`.
-/

namespace MailboxActors.Examples.Anoma.Identity

variable (A : AnomaTypes)

-- ============================================================================
-- § Identity (identity management)
-- ============================================================================

/-- Capability flags for an identity. -/
inductive Capability where
  | commit    : Capability
  | decrypt   : Capability
  | both      : Capability
  deriving DecidableEq, BEq

/-- Messages for the identity-management engine. -/
inductive IdentityMsg where
  | generateReq  : A.Backend → Capability → IdentityMsg
  | generateReply : A.ExternalIdentity → IdentityMsg
  | deleteReq    : A.ExternalIdentity → IdentityMsg
  | deleteReply   : Bool → IdentityMsg
  deriving DecidableEq, BEq

/-- Configuration for the identity-management engine. -/
abbrev IdentityCfg := Unit

/-- Local state for the identity-management engine. -/
structure IdentityState where
  nextId : Nat

-- ============================================================================
-- § Commitment (signature generation)
-- ============================================================================

/-- Messages for the commitment engine. -/
inductive CommitmentMsg where
  | signReq   : A.Signable → CommitmentMsg
  | signReply  : A.Signature → CommitmentMsg
  deriving DecidableEq, BEq

/-- Configuration for the commitment engine. -/
structure CommitmentCfg where
  backend : A.Backend

/-- Local state for the commitment engine (stateless). -/
abbrev CommitmentState := Unit

-- ============================================================================
-- § Decryption
-- ============================================================================

/-- Messages for the decryption engine. -/
inductive DecryptionMsg where
  | decryptReq   : A.Ciphertext → DecryptionMsg
  | decryptReply  : A.Plaintext → DecryptionMsg
  deriving DecidableEq, BEq

/-- Configuration for the decryption engine. -/
structure DecryptionCfg where
  backend : A.Backend

/-- Local state for the decryption engine (stateless). -/
abbrev DecryptionState := Unit

-- ============================================================================
-- § Verification
-- ============================================================================

/-- Messages for the verification engine. -/
inductive VerificationMsg where
  | verifyReq   : A.ExternalIdentity → A.Signable → A.Signature → Bool → VerificationMsg
  | verifyReply  : Bool → VerificationMsg
  deriving DecidableEq, BEq

/-- Configuration for the verification engine. -/
structure VerificationCfg where
  backend : A.Backend

/-- Local state for the verification engine (stateless). -/
abbrev VerificationState := Unit

-- ============================================================================
-- § Encryption
-- ============================================================================

/-- Messages for the encryption engine. -/
inductive EncryptionMsg where
  | encryptReq   : A.ExternalIdentity → A.Plaintext → Bool → EncryptionMsg
  | encryptReply  : A.Ciphertext → EncryptionMsg
  deriving DecidableEq, BEq

/-- Configuration for the encryption engine. -/
structure EncryptionCfg where
  backend : A.Backend

/-- Local state for the encryption engine (stateless). -/
abbrev EncryptionState := Unit

-- ============================================================================
-- § Evidence-based engines (shared pattern)
-- ============================================================================

/-- Shared message type for delegation/naming evidence engines.
    Used by `signDeleg`, `readDeleg`, and `nameRegistry`. -/
inductive EvidenceMsg (E : Type) where
  | query   : A.ExternalIdentity → EvidenceMsg E
  | reply   : Bool → EvidenceMsg E
  | submit  : E → EvidenceMsg E
  | confirm : Bool → EvidenceMsg E
  deriving DecidableEq, BEq

-- ============================================================================
-- § SignDeleg (signs-for delegation)
-- ============================================================================

abbrev SignDelegMsg := EvidenceMsg A A.SignEvidence
abbrev SignDelegCfg := Unit
structure SignDelegState where
  evidenceCount : Nat

-- ============================================================================
-- § ReadDeleg (reads-for delegation)
-- ============================================================================

abbrev ReadDelegMsg := EvidenceMsg A A.ReadEvidence
abbrev ReadDelegCfg := Unit
structure ReadDelegState where
  evidenceCount : Nat

-- ============================================================================
-- § NameRegistry (naming)
-- ============================================================================

abbrev NameRegistryMsg := EvidenceMsg A A.NameEvidence
abbrev NameRegistryCfg := Unit
structure NameRegistryState where
  registrationCount : Nat

end MailboxActors.Examples.Anoma.Identity
