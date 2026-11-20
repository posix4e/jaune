import Jaune.MessageCall.Exec

/-!
# The top-level frame

A top-level message call runs one frame whose checkpoint is the state its message was prepared
on: `initDevm` of the message, or under Amsterdam's rules the state `prepareTopLevelAmsterdam`
returns. `Frame.runTop` enters it from that checkpoint, runs `exec` and settles. The transaction
reads the settled `Frame.Result` through `Frame.output` and `Frame.outputAmsterdam`.

`Msg` is the top-level message type, and `Message.ofTop` builds the frame's message from it.
-/

namespace Jaune

open Jaune

/-- A top-level `Msg` as a frame message. `isCreate` gives the kind; it is the frame's flag,
not the message's. -/
def Message.ofTop (msg : Msg) (isCreate : Bool) : Message :=
  { context :=
      { caller := msg.caller, recipient := msg.currentTarget, value := msg.value
        calldata := msg.data, code := msg.code, depthLeft := msg.depth
        isStatic := msg.isStatic, tx := msg.tenv.stat, block := msg.benv.stat }
    kind := if isCreate then .create else .call
    codeAddress := msg.codeAddress
    target := msg.target
    gas := msg.gas
    stateGasGrant := msg.stateGasGrant
    transfersValue := msg.shouldTransferValue
    disablePrecompiles := msg.disablePrecompiles }

/-- A top-level frame: the checkpoint is the state its message starts on. -/
def Frame.ofTop (msg : Msg) (isCreate : Bool) : Frame :=
  ⟨Message.ofTop msg isCreate, Frame.State.ofDevm (initDevm msg)⟩

/-- Run a top-level frame: enter it from its checkpoint, run the code, settle. -/
def Frame.runTop (f : Frame) : Except Fault Frame.Result :=
  match enterWith f f.checkpoint.toDevm with
  | .done result => result
  | .run evm => settle f (exec evm)

/-- The refund counter a top-level result reports: a success's substate refund (an internal fault
if negative), a failure's zero. -/
def Frame.Result.refundCounter : Frame.Result → Except EvmError Nat
  | .success _ _ _ _ substate _ =>
    (Int.toNat? substate.refund).toExcept
      (EvmError.internal (.invariant (.text "refund counter is negative")))
  | _ => .ok 0

/-- The accounts read in preparing a top-level message, before a frame exists to record them: the
account the message is sent to; the account whose code it runs, which is another one when the first
delegates; and the account each EIP-7702 authorization is signed by, under the three conditions
`setDelegationStep` reads it (a chain id that applies, a nonce that can be raised, a signature that
recovers). The signatures are recovered a second time here, to leave `Msg` and that step as they are. -/
def Message.preparationReads (m : Message) : List Address :=
  let authorities := m.context.tx.auths.filterMap fun auth =>
    if auth.chainId != m.context.block.chainId.toU256 && auth.chainId != 0 then none
    else if auth.nonce = UInt64.max then none
    else (recoverAuthority auth).toOption
  m.context.recipient :: (m.codeAddress.toList ++ authorities)

/-- What a top-level frame hands the transaction under rules without state gas. A call adds its
authorization refund; a failed frame keeps no log, deletion or touch. The read sets and the explicit
writes are handed over in every outcome, as under state gas: a caller that executed against a state known
only in part has to see what a failed transaction read as much as what a successful one did, and what
was read before the frame began. -/
def Frame.output (f : Frame) (authorizationRefund : Nat) (r : Frame.Result) :
    Except EvmError (Jaune.State × MsgCallOutput) := do
  let refund ← r.refundCounter
  let (logs, accountsToDelete, touchedAccounts) := match r with
    | .success _ _ _ _ substate _ =>
      (substate.logs, substate.selfDestructs, substate.touchedAccounts)
    | _ => ([], .emptyWithCapacity, .emptyWithCapacity)
  .ok ⟨(f.worldAfter r).state, {
    accountReads := f.message.preparationReads.foldl (fun set a => set.insert a) r.trail.accountReads
    storageReads := r.trail.storageReads
    storageWrites := (f.worldAfter r).storageWrites
    gasLeft := r.gasLeft, refundCounter := authorizationRefund + refund,
    logs, accountsToDelete, error := r.error?, returnData := r.output, touchedAccounts }⟩

/-- What a top-level frame hands the transaction under rules with state gas: the read sets and the
explicit writes in every outcome, the state-gas meter, and no touched accounts. -/
def Frame.outputAmsterdam (f : Frame) (r : Frame.Result) :
    Except EvmError (Jaune.State × MsgCallOutput) := do
  let refundCounter ← r.refundCounter
  let (logs, accountsToDelete) := match r with
    | .success _ _ _ _ substate _ => (substate.logs, substate.selfDestructs)
    | _ => ([], .emptyWithCapacity)
  let stateGasUsed :=
    Int.ofNat f.message.stateGasGrant - Int.ofNat r.stateGas.left +
      Int.ofNat r.stateGas.spilled + Int.ofNat r.stateGas.committedSpill
  .ok ⟨(f.worldAfter r).state, {
    accountReads := r.trail.accountReads
    storageReads := r.trail.storageReads
    storageWrites := (f.worldAfter r).storageWrites
    gasLeft := r.gasLeft
    refundCounter := refundCounter
    logs := logs
    accountsToDelete := accountsToDelete
    error := r.error?
    returnData := r.output
    stateGasLeft := r.stateGas.left
    stateGasUsed := stateGasUsed
  }⟩

end Jaune
