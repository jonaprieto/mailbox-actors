import MailboxActors.System.Node
import MailboxActors.Engine.Message

/-!
# System State
-/

namespace MailboxActors

variable [EngineSpec]

/-- System state `κ = (N, M, Ω)`. -/
structure SystemState where
  nodes : List Node
  messages : List Message
  /-- Monotonic counter for fresh identifier generation. -/
  nextId : Nat

/-- Generate a fresh identifier and advance the counter. -/
def SystemState.freshId (κ : SystemState) : Nat × SystemState :=
  (κ.nextId, { κ with nextId := κ.nextId + 1 })

/-- The `mailboxOf` mapping: returns the mailbox address for a processing
    engine.  Modelled as a total function on addresses. -/
def SystemState.mailboxOf (_κ : SystemState) (addr : Address) : Address :=
  -- Convention: the paired mailbox has engineId = addr.engineId + 1
  -- on the same node (matching S-SpawnWithMailbox's sequential allocation).
  { addr with engineId := addr.engineId + 1 }

lemma mailboxOf_ne_self (κ : SystemState) (addr : Address) :
    κ.mailboxOf addr ≠ addr := by
  intro h
  have : (κ.mailboxOf addr).engineId = addr.engineId := by rw [h]
  simp [SystemState.mailboxOf] at this

lemma mailboxOf_injective (κ : SystemState) {addr addr' : Address}
    (h : κ.mailboxOf addr = κ.mailboxOf addr') : addr = addr' := by
  have h1 : (κ.mailboxOf addr).nodeId = (κ.mailboxOf addr').nodeId := by rw [h]
  have h2 : (κ.mailboxOf addr).engineId = (κ.mailboxOf addr').engineId := by rw [h]
  simp only [SystemState.mailboxOf, Nat.add_right_cancel_iff] at h1 h2
  cases addr; cases addr'; simp only [Address.mk.injEq]; exact ⟨h1, h2⟩

/-- Look up an engine globally by its address. -/
def SystemState.engineAt (κ : SystemState) (addr : Address) : Option SomeEngine :=
  match κ.nodes.find? (fun n => n.id == addr.nodeId) with
  | some node => node.getEngine addr.engineId
  | none => none

/-- The initial (empty) system state. -/
def SystemState.initial : SystemState :=
  { nodes := [], messages := [], nextId := 0 }

/-- `find?`-then-`getEngine` is stable under appending a node with empty engines. -/
lemma find?_match_append_emptyEngines (nodes : List Node) (emptyNode : Node)
    (hn : emptyNode.engines = []) (p : Node → Bool) (eid : Nat) :
    (match (nodes ++ [emptyNode]).find? p with
     | some node => node.getEngine eid
     | none => none) =
    (match nodes.find? p with
     | some node => node.getEngine eid
     | none => none) := by
  induction nodes with
  | nil =>
    simp only [List.nil_append, List.find?_nil]
    cases hp : p emptyNode
    · simp [hp]
    · simp [hp, Node.getEngine, hn]
  | cons hd tl ih =>
    simp only [List.cons_append]
    cases hp : p hd
    · simp only [List.find?_cons, hp]; exact ih
    · simp only [List.find?_cons, hp]

/-- Appending a node with empty engines preserves all engine lookups. -/
lemma engineAt_append_emptyNode (κ : SystemState) (addr : Address) :
    SystemState.engineAt
      ⟨κ.nodes ++ [{ id := κ.nextId, engines := [] }], κ.messages, κ.nextId + 1⟩ addr =
    κ.engineAt addr := by
  unfold SystemState.engineAt
  exact find?_match_append_emptyEngines κ.nodes ⟨κ.nextId, []⟩ rfl _ _

-- ============================================================================
-- § Engine Update Operations
-- ============================================================================

/-- Replace the engine at `localId` in a node's engine map.
    If `localId` is not present, the node is unchanged. -/
def Node.setEngine (n : Node) (localId : Nat) (se : SomeEngine) : Node :=
  { n with engines := n.engines.map fun p =>
      if p.1 == localId then (localId, se) else p }

@[simp] lemma Node.setEngine_id (n : Node) (localId : Nat) (se : SomeEngine) :
    (n.setEngine localId se).id = n.id := rfl

/-- Update the engine at a given address in the system state. -/
def SystemState.updateEngineAt (κ : SystemState) (addr : Address)
    (se : SomeEngine) : SystemState :=
  { κ with nodes := κ.nodes.map fun n =>
      if n.id == addr.nodeId then n.setEngine addr.engineId se else n }

@[simp] lemma SystemState.updateEngineAt_messages (κ : SystemState)
    (addr : Address) (se : SomeEngine) :
    (κ.updateEngineAt addr se).messages = κ.messages := rfl

/-- Overriding `messages` does not affect `engineAt` (which depends only on `nodes`). -/
@[simp] lemma SystemState.withMessages_engineAt (κ : SystemState) (ms : List Message)
    (addr : Address) :
    ({ κ with messages := ms } : SystemState).engineAt addr = κ.engineAt addr := rfl

/-- `mailboxOf` ignores the state entirely, so overriding messages preserves it. -/
@[simp] lemma SystemState.withMessages_mailboxOf (κ : SystemState) (ms : List Message)
    (addr : Address) :
    ({ κ with messages := ms } : SystemState).mailboxOf addr = κ.mailboxOf addr := rfl

/-- `mailboxOf` ignores the state entirely, so `updateEngineAt` preserves it. -/
@[simp] lemma SystemState.updateEngineAt_mailboxOf (κ : SystemState)
    (target addr : Address) (se : SomeEngine) :
    (κ.updateEngineAt target se).mailboxOf addr = κ.mailboxOf addr := rfl

@[simp] lemma SystemState.updateEngineAt_nextId (κ : SystemState)
    (addr : Address) (se : SomeEngine) :
    (κ.updateEngineAt addr se).nextId = κ.nextId := rfl

-- ── BEq helper ──

omit [EngineSpec] in
private lemma beq_false_of_ne [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) :
    (a == b) = false := by
  match h' : a == b with
  | true => exact absurd (eq_of_beq h') h
  | false => rfl

-- ── List-level helpers for setEngine ──

private lemma map_find_setEngine_self (engines : EngineMap) (id : Nat)
    (se : SomeEngine) :
    engines.find? (fun p => p.1 == id) ≠ none →
    (engines.map fun p => if p.1 == id then (id, se) else p).find?
      (fun p => p.1 == id) = some (id, se) := by
  intro h
  induction engines with
  | nil => exact absurd rfl h
  | cons e es ih =>
    simp only [List.map_cons, List.find?_cons]
    match he : e.1 == id with
    | true =>
      simp only [↓reduceIte, beq_self_eq_true]
    | false =>
      simp only [he, ↓reduceIte, Bool.false_eq_true]
      simp only [List.find?_cons, he] at h
      exact ih h

private lemma map_find_setEngine_ne (engines : EngineMap) (id id' : Nat)
    (se : SomeEngine) (h : id' ≠ id) :
    (engines.map fun p => if p.1 == id then (id, se) else p).find?
      (fun p => p.1 == id') = engines.find? (fun p => p.1 == id') := by
  induction engines with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.find?_cons]
    match he : e.1 == id with
    | true =>
      simp only [↓reduceIte]
      have hne : (id == id') = false := beq_false_of_ne (Ne.symm h)
      simp only [hne]
      have : (e.1 == id') = false := by
        rw [eq_of_beq he]; exact beq_false_of_ne (Ne.symm h)
      simp only [this]
      exact ih
    | false =>
      match he' : e.1 == id' with
      | true => rfl
      | false => exact ih

-- ── System-level engineAt after updateEngineAt ──

/-- `engineAt` traversal for `updateEngineAt`: induction on the node list. -/
private lemma engineAt_updateEngineAt_aux (nodes : List Node)
    (nodeId engId : Nat) (se : SomeEngine) (targetNodeId targetEngId : Nat) :
    (match (nodes.map fun n =>
        if n.id == nodeId then n.setEngine engId se else n).find?
        (fun n => n.id == targetNodeId) with
      | some node => node.getEngine targetEngId
      | none => none) =
    if nodeId == targetNodeId then
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => (node.setEngine engId se).getEngine targetEngId
        | none => none)
    else
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => node.getEngine targetEngId
        | none => none) := by
  induction nodes with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.find?_cons]
    match hn : n.id == nodeId with
    | true =>
      simp only [↓reduceIte]
      match ht : n.id == targetNodeId with
      | true =>
        have hnt : (nodeId == targetNodeId) = true := by
          have := eq_of_beq hn; have := eq_of_beq ht; subst_vars
          exact beq_self_eq_true _
        simp [hnt]
      | false => exact ih
    | false =>
      match ht : n.id == targetNodeId with
      | true =>
        match hnt : nodeId == targetNodeId with
        | true =>
          exfalso
          have := eq_of_beq hnt; have := eq_of_beq ht; subst_vars
          simp at hn
        | false => rfl
      | false => exact ih

/-- After updating the engine at `addr` to `se`, looking up `addr` yields `se`,
    provided the engine existed before. -/
theorem engineAt_updateEngineAt_self (κ : SystemState) (addr : Address)
    (se : SomeEngine) (h : ∃ old, κ.engineAt addr = some old) :
    (κ.updateEngineAt addr se).engineAt addr = some se := by
  obtain ⟨old, hold⟩ := h
  simp only [SystemState.engineAt, SystemState.updateEngineAt] at *
  rw [engineAt_updateEngineAt_aux]
  simp only [beq_self_eq_true, ↓reduceIte]
  cases hfind : κ.nodes.find? (fun n => n.id == addr.nodeId) with
  | none => rw [hfind] at hold; simp at hold
  | some node =>
    rw [hfind] at hold
    simp only [Node.getEngine, Node.setEngine] at *
    rw [map_find_setEngine_self]
    · simp
    · intro habs; simp [habs] at hold

/-- Updating the engine at `addr` does not affect lookups at a different address. -/
theorem engineAt_updateEngineAt_ne (κ : SystemState) (addr addr' : Address)
    (se : SomeEngine) (h : addr' ≠ addr) :
    (κ.updateEngineAt addr se).engineAt addr' = κ.engineAt addr' := by
  simp only [SystemState.engineAt, SystemState.updateEngineAt] at *
  rw [engineAt_updateEngineAt_aux]
  match hnode : addr.nodeId == addr'.nodeId with
  | true =>
    simp only [↓reduceIte]
    cases hfind : κ.nodes.find? (fun n => n.id == addr'.nodeId) with
    | none => rfl
    | some node =>
      simp only [Node.getEngine, Node.setEngine]
      rw [map_find_setEngine_ne]
      intro heq
      exact absurd (show addr' = addr by
        rcases addr with ⟨n1, e1⟩; rcases addr' with ⟨n2, e2⟩
        simp only [Address.mk.injEq]; dsimp only at *
        exact ⟨(eq_of_beq hnode).symm, heq⟩) h
  | false =>
    simp

-- ============================================================================
-- § Engine Removal Operations
-- ============================================================================

/-- Remove the engine at `localId` from a node's engine map. -/
def Node.removeEngine (n : Node) (localId : Nat) : Node :=
  { n with engines := n.engines.filter fun p => !(p.1 == localId) }

@[simp] lemma Node.removeEngine_id (n : Node) (localId : Nat) :
    (n.removeEngine localId).id = n.id := rfl

/-- Remove the engine at a given address from the system state. -/
def SystemState.removeEngineAt (κ : SystemState) (addr : Address) : SystemState :=
  { κ with nodes := κ.nodes.map fun n =>
      if n.id == addr.nodeId then n.removeEngine addr.engineId else n }

@[simp] lemma SystemState.removeEngineAt_messages (κ : SystemState)
    (addr : Address) :
    (κ.removeEngineAt addr).messages = κ.messages := rfl

@[simp] lemma SystemState.removeEngineAt_nextId (κ : SystemState)
    (addr : Address) :
    (κ.removeEngineAt addr).nextId = κ.nextId := rfl

-- ── List-level helpers for removeEngine ──

private lemma filter_find_removeEngine_self (engines : EngineMap) (id : Nat) :
    (engines.filter fun p => !(p.1 == id)).find? (fun p => p.1 == id) = none := by
  induction engines with
  | nil => simp
  | cons e es ih =>
    simp only [List.filter_cons]
    match he : e.1 == id with
    | true =>
      simp only [Bool.not_true]
      exact ih
    | false =>
      simp only [Bool.not_false, ↓reduceIte, List.find?_cons, he]
      exact ih

private lemma filter_find_removeEngine_ne (engines : EngineMap) (id id' : Nat)
    (h : id' ≠ id) :
    (engines.filter fun p => !(p.1 == id)).find? (fun p => p.1 == id') =
    engines.find? (fun p => p.1 == id') := by
  induction engines with
  | nil => simp
  | cons e es ih =>
    simp only [List.filter_cons, List.find?_cons]
    match he : e.1 == id with
    | true =>
      simp only [Bool.not_true]
      have : (e.1 == id') = false := by
        rw [eq_of_beq he]; exact beq_false_of_ne (Ne.symm h)
      simp only [this]
      exact ih
    | false =>
      simp only [Bool.not_false, ↓reduceIte, List.find?_cons]
      match he' : e.1 == id' with
      | true => rfl
      | false =>
        exact ih

-- ── System-level engineAt after removeEngineAt ──

/-- `engineAt` traversal for `removeEngineAt`: induction on the node list. -/
private lemma engineAt_removeEngineAt_aux (nodes : List Node)
    (nodeId engId : Nat) (targetNodeId targetEngId : Nat) :
    (match (nodes.map fun n =>
        if n.id == nodeId then n.removeEngine engId else n).find?
        (fun n => n.id == targetNodeId) with
      | some node => node.getEngine targetEngId
      | none => none) =
    if nodeId == targetNodeId then
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => (node.removeEngine engId).getEngine targetEngId
        | none => none)
    else
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => node.getEngine targetEngId
        | none => none) := by
  induction nodes with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.find?_cons]
    match hn : n.id == nodeId with
    | true =>
      simp only [↓reduceIte]
      match ht : n.id == targetNodeId with
      | true =>
        have hnt : (nodeId == targetNodeId) = true := by
          have := eq_of_beq hn; have := eq_of_beq ht
          subst_vars; exact beq_self_eq_true _
        simp [hnt]
      | false => exact ih
    | false =>
      match ht : n.id == targetNodeId with
      | true =>
        match hnt : nodeId == targetNodeId with
        | true =>
          exfalso
          have := eq_of_beq hnt; have := eq_of_beq ht; subst_vars
          simp at hn
        | false => rfl
      | false => exact ih

/-- After removing the engine at `addr`, looking up `addr` yields `none`. -/
theorem engineAt_removeEngineAt_self (κ : SystemState) (addr : Address) :
    (κ.removeEngineAt addr).engineAt addr = none := by
  simp only [SystemState.engineAt, SystemState.removeEngineAt]
  rw [engineAt_removeEngineAt_aux]
  simp only [beq_self_eq_true, ↓reduceIte]
  cases hfind : κ.nodes.find? (fun n => n.id == addr.nodeId) with
  | none => rfl
  | some node =>
    simp only [Node.getEngine, Node.removeEngine]
    rw [filter_find_removeEngine_self]
    simp

/-- Removing the engine at `addr` does not affect lookups at a different address. -/
theorem engineAt_removeEngineAt_ne (κ : SystemState) (addr addr' : Address)
    (h : addr' ≠ addr) :
    (κ.removeEngineAt addr).engineAt addr' = κ.engineAt addr' := by
  simp only [SystemState.engineAt, SystemState.removeEngineAt]
  rw [engineAt_removeEngineAt_aux]
  match hnode : addr.nodeId == addr'.nodeId with
  | true =>
    simp only [↓reduceIte]
    cases hfind : κ.nodes.find? (fun n => n.id == addr'.nodeId) with
    | none => rfl
    | some node =>
      simp only [Node.getEngine, Node.removeEngine]
      rw [filter_find_removeEngine_ne]
      intro heq
      exact absurd (show addr' = addr by
        rcases addr with ⟨n1, e1⟩; rcases addr' with ⟨n2, e2⟩
        simp only [Address.mk.injEq]; dsimp only at *
        exact ⟨(eq_of_beq hnode).symm, heq⟩) h
  | false =>
    simp

-- ============================================================================
-- § Engine Addition Operations
-- ============================================================================

/-- Append a new engine entry to a node's engine map. -/
def Node.addEngine (n : Node) (localId : Nat) (se : SomeEngine) : Node :=
  { n with engines := n.engines ++ [(localId, se)] }

@[simp] lemma Node.addEngine_id (n : Node) (localId : Nat) (se : SomeEngine) :
    (n.addEngine localId se).id = n.id := rfl

/-- Add an engine at a given address in the system state.
    The node at `addr.nodeId` must already exist. -/
def SystemState.addEngineAt (κ : SystemState) (addr : Address)
    (se : SomeEngine) : SystemState :=
  { κ with nodes := κ.nodes.map fun n =>
      if n.id == addr.nodeId then n.addEngine addr.engineId se else n }

@[simp] lemma SystemState.addEngineAt_messages (κ : SystemState)
    (addr : Address) (se : SomeEngine) :
    (κ.addEngineAt addr se).messages = κ.messages := rfl

@[simp] lemma SystemState.addEngineAt_nextId (κ : SystemState)
    (addr : Address) (se : SomeEngine) :
    (κ.addEngineAt addr se).nextId = κ.nextId := rfl

@[simp] lemma SystemState.addEngineAt_mailboxOf (κ : SystemState)
    (target addr : Address) (se : SomeEngine) :
    (κ.addEngineAt target se).mailboxOf addr = κ.mailboxOf addr := rfl

-- ── withNextId simp lemmas ──

@[simp] lemma SystemState.withNextId_engineAt (κ : SystemState) (n : Nat)
    (addr : Address) :
    ({ κ with nextId := n } : SystemState).engineAt addr = κ.engineAt addr := rfl

@[simp] lemma SystemState.withNextId_messages (κ : SystemState) (n : Nat) :
    ({ κ with nextId := n } : SystemState).messages = κ.messages := rfl

@[simp] lemma SystemState.withNextId_mailboxOf (κ : SystemState) (n : Nat)
    (addr : Address) :
    ({ κ with nextId := n } : SystemState).mailboxOf addr = κ.mailboxOf addr := rfl

-- ── List-level helpers for addEngine ──

private lemma append_find_addEngine_self (engines : EngineMap) (id : Nat)
    (se : SomeEngine)
    (h : engines.find? (fun p => p.1 == id) = none) :
    (engines ++ [(id, se)]).find? (fun p => p.1 == id) = some (id, se) := by
  induction engines with
  | nil => simp
  | cons e es ih =>
    simp only [List.find?_cons] at h
    match he : e.1 == id with
    | true => simp [he] at h
    | false =>
      simp only [he] at h
      simp only [List.cons_append, List.find?_cons, he]
      exact ih h

private lemma append_find_addEngine_ne (engines : EngineMap) (id id' : Nat)
    (se : SomeEngine) (h : id' ≠ id) :
    (engines ++ [(id, se)]).find? (fun p => p.1 == id') =
    engines.find? (fun p => p.1 == id') := by
  induction engines with
  | nil =>
    simp only [List.nil_append, List.find?_cons, List.find?_nil]
    have : (id == id') = false := beq_false_of_ne (Ne.symm h)
    simp [this]
  | cons e es ih =>
    simp only [List.cons_append, List.find?_cons]
    match he : e.1 == id' with
    | true => rfl
    | false =>
      exact ih

-- ── System-level engineAt after addEngineAt ──

/-- `engineAt` traversal for `addEngineAt`: induction on the node list. -/
private lemma engineAt_addEngineAt_aux (nodes : List Node)
    (nodeId engId : Nat) (se : SomeEngine) (targetNodeId targetEngId : Nat) :
    (match (nodes.map fun n =>
        if n.id == nodeId then n.addEngine engId se else n).find?
        (fun n => n.id == targetNodeId) with
      | some node => node.getEngine targetEngId
      | none => none) =
    if nodeId == targetNodeId then
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => (node.addEngine engId se).getEngine targetEngId
        | none => none)
    else
      (match nodes.find? (fun n => n.id == targetNodeId) with
        | some node => node.getEngine targetEngId
        | none => none) := by
  induction nodes with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.find?_cons]
    match hn : n.id == nodeId with
    | true =>
      simp only [↓reduceIte]
      match ht : n.id == targetNodeId with
      | true =>
        have hnt : (nodeId == targetNodeId) = true := by
          have := eq_of_beq hn; have := eq_of_beq ht; subst_vars
          exact beq_self_eq_true _
        simp [hnt]
      | false => exact ih
    | false =>
      match ht : n.id == targetNodeId with
      | true =>
        match hnt : nodeId == targetNodeId with
        | true =>
          exfalso
          have := eq_of_beq hnt; have := eq_of_beq ht; subst_vars
          simp at hn
        | false => rfl
      | false => exact ih

/-- After adding an engine at `addr`, looking up `addr` yields the new engine,
    provided the address was fresh and the node exists. -/
theorem engineAt_addEngineAt_self (κ : SystemState) (addr : Address)
    (se : SomeEngine)
    (hfresh : κ.engineAt addr = none)
    (hnode : ∃ n ∈ κ.nodes, n.id = addr.nodeId) :
    (κ.addEngineAt addr se).engineAt addr = some se := by
  obtain ⟨node, hnode_mem, hnode_id⟩ := hnode
  simp only [SystemState.engineAt, SystemState.addEngineAt] at *
  rw [engineAt_addEngineAt_aux]
  simp only [beq_self_eq_true, ↓reduceIte]
  have hfind : κ.nodes.find? (fun n => n.id == addr.nodeId) ≠ none := by
    intro habs
    exact absurd (List.find?_eq_none.mp habs node hnode_mem) (by simp [hnode_id])
  cases hfind' : κ.nodes.find? (fun n => n.id == addr.nodeId) with
  | none => exact absurd hfind' hfind
  | some node' =>
    -- hfresh reduces to: node'.getEngine addr.engineId = none
    have hge : node'.getEngine addr.engineId = none := by rw [hfind'] at hfresh; exact hfresh
    simp only [Node.getEngine, Node.addEngine]
    have hfresh' : node'.engines.find? (fun p => p.1 == addr.engineId) = none := by
      unfold Node.getEngine at hge
      match hf : node'.engines.find? (fun p => p.1 == addr.engineId) with
      | none => exact hf
      | some val => rw [hf] at hge; exact absurd hge (by simp)
    rw [append_find_addEngine_self _ _ _ hfresh']
    simp

/-- Adding an engine at `addr` does not affect lookups at a different address. -/
theorem engineAt_addEngineAt_ne (κ : SystemState) (addr addr' : Address)
    (se : SomeEngine) (h : addr' ≠ addr) :
    (κ.addEngineAt addr se).engineAt addr' = κ.engineAt addr' := by
  simp only [SystemState.engineAt, SystemState.addEngineAt] at *
  rw [engineAt_addEngineAt_aux]
  match hnode : addr.nodeId == addr'.nodeId with
  | true =>
    simp only [↓reduceIte]
    cases hfind : κ.nodes.find? (fun n => n.id == addr'.nodeId) with
    | none => rfl
    | some node =>
      simp only [Node.getEngine, Node.addEngine]
      rw [append_find_addEngine_ne]
      intro heq
      exact absurd (show addr' = addr by
        rcases addr with ⟨n1, e1⟩; rcases addr' with ⟨n2, e2⟩
        simp only [Address.mk.injEq]; dsimp only at *
        exact ⟨(eq_of_beq hnode).symm, heq⟩) h
  | false =>
    simp

/-- If an engine exists at `addr`, then its node must exist in the system. -/
lemma node_exists_of_engineAt (κ : SystemState) (addr : Address) :
    κ.engineAt addr ≠ none → ∃ n ∈ κ.nodes, n.id = addr.nodeId := by
  unfold SystemState.engineAt
  match hfind : κ.nodes.find? (fun n => n.id == addr.nodeId) with
  | some n =>
    intro _
    refine ⟨n, List.mem_of_find?_eq_some hfind, ?_⟩
    have := List.find?_some hfind
    simp only [beq_iff_eq] at this
    exact this
  | none =>
    simp [hfind]

/-- Adding an engine preserves node membership (by id). -/
lemma addEngineAt_node_mem (κ : SystemState) (addr : Address) (se : SomeEngine)
    (nodeId : Nat) (h : ∃ n ∈ κ.nodes, n.id = nodeId) :
    ∃ n ∈ (κ.addEngineAt addr se).nodes, n.id = nodeId := by
  obtain ⟨n, hn, hid⟩ := h
  simp only [SystemState.addEngineAt]
  let f := fun n' : Node =>
    if n'.id == addr.nodeId then n'.addEngine addr.engineId se else n'
  refine ⟨f n, List.mem_map.mpr ⟨n, hn, rfl⟩, ?_⟩
  simp only [f]
  split <;> simp [hid]

end MailboxActors
