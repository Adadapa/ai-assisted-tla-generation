```tla
---- MODULE SmartBFT ----
EXTENDS Naturals, FiniteSets, Sequences, TLC, FiniteSetsExt

(* -- Constants -- *)
CONSTANT Nodes, f
CONSTANT Nil (* Represents an uninitialized or absent value *)

(* Phases for normal operation *)
CONSTANT IDLE, PREPARED, COMMITTED

(* Phases for view change *)
CONSTANT VIEW_CHANGE_PHASE, VIEW_DATA_PHASE, NEW_VIEW_PHASE

(* -- Variables -- *)
VARIABLES
    currentView,          (* Global current view number, highest agreed view *)
    currentSequence,      (* Global highest sequence number ever proposed *)
    replicaState,         (* Map: NodeID -> ReplicaStateRecord *)
    messages,             (* Set of messages in transit *)
    requests,             (* Set of client requests waiting to be processed *)
    decidedProposals      (* Map: SequenceNumber -> Proposal that has been decided *)

(* -- Helper Functions -- *)

(* N is the total number of nodes *)
N == Cardinality(Nodes)

(* Quorum size: 2f + 1 *)
QuorumSize == 2*f + 1

(*
  getLeaderID determines the leader for a given view.
  Simplified: (viewNumber mod N) + 1.
  Assumes Nodes are {1, ..., N}.
  Excludes DecisionsPerLeader, NodesList, BlackList as per requirements.
*)
getLeaderID(viewNum) == (viewNum % N) + 1

(* Checks if a set of nodes forms a quorum *)
IsQuorum(S) == Cardinality(S) >= QuorumSize

(* Max of two numbers *)
Max2(a, b) == IF a >= b THEN a ELSE b

(* -- State Records and Message Types -- *)

(* ReplicaStateRecord for each node *)
ReplicaStateRecord ==
    [ view              : Nat,
      seq               : Nat, (* Highest sequence number this replica has prepared for in current view *)
      phase             : [Nat -> {IDLE, PREPARED, COMMITTED}], (* Phase per sequence number *)
      preparedMessages  : [Nat -> SUBSET (Nodes \X PreprepareMsgType)], (* Stores (sender, PreprepareMsg) for Prepare quorum *)
      commitMessages    : [Nat -> SUBSET (Nodes \X CommitMsgType)],    (* Stores (sender, CommitMsg) for Commit quorum *)
      lastDecidedSeq    : Nat, (* Highest sequence number this replica has decided *)
      lastDecidedView   : Nat, (* View of the last decided sequence *)
      viewChangePhase   : {IDLE, VIEW_CHANGE_PHASE, VIEW_DATA_PHASE, NEW_VIEW_PHASE},
      viewChangeSent    : BOOLEAN,
      viewDataSent      : BOOLEAN,
      viewChangeQuorum  : [Nat -> SUBSET (Nodes \X ViewChangeMsgType)], (* Stores (sender, ViewChangeMsg) for ViewChange quorum *)
      viewDataQuorum    : [Nat -> SUBSET (Nodes \X ViewDataMsgType)],   (* Stores (sender, ViewDataMsg) for ViewData quorum *)
      lastProposal      : [Nat -> ProposalType \cup {Nil}] (* Last proposal seen/processed for a sequence *)
    ]

(* Message Types *)
ProposalType == [
    metadata : [view : Nat, seq : Nat],
    batch    : SUBSET RequestType
]

RequestType == STRING (* Simplified: client requests are just strings *)

PreprepareMsgType == [
    type     : {"Preprepare"},
    view     : Nat,
    seq      : Nat,
    proposal : ProposalType
]

PrepareMsgType == [
    type        : {"Prepare"},
    view        : Nat,
    seq         : Nat,
    proposalHash: ProposalType (* Simplified: hash of proposal, using proposal itself *)
]

CommitMsgType == [
    type        : {"Commit"},
    view        : Nat,
    seq         : Nat,
    proposalHash: ProposalType (* Simplified: hash of proposal, using proposal itself *)
]

ViewChangeMsgType == [
    type            : {"ViewChange"},
    view            : Nat,
    lastDecidedSeq  : Nat,
    lastDecidedView : Nat,
    inFlightProposal: ProposalType \cup {Nil} (* The proposal the node was trying to commit *)
]

ViewDataMsgType == [
    type            : {"ViewData"},
    view            : Nat,
    sender          : Nodes,
    lastDecidedSeq  : Nat,
    lastDecidedView : Nat,
    inFlightProposal: ProposalType \cup {Nil}
]

NewViewMsgType == [
    type            : {"NewView"},
    view            : Nat,
    newProposalSequence : Nat,
    newDecisionsInView  : Nat, (* Not explicitly modeled, but kept for consistency with source *)
    proposal        : ProposalType (* The proposal for the first sequence in the new view *)
]

MessageType == PreprepareMsgType \cup PrepareMsgType \cup CommitMsgType \cup ViewChangeMsgType \cup ViewDataMsgType \cup NewViewMsgType

MessageInTransit == [
    sender   : Nodes,
    receiver : Nodes,
    content  : MessageType
]

(* -- Initial State -- *)
Init ==
    /\ currentView = 0
    /\ currentSequence = 0
    /\ replicaState = [n \in Nodes |->
                        [ view              |-> 0,
                          seq               |-> 0,
                          phase             |-> [s \in Nat |-> IDLE],
                          preparedMessages  |-> [s \in Nat |-> {}],
                          commitMessages    |-> [s \in Nat |-> {}],
                          lastDecidedSeq    |-> 0,
                          lastDecidedView   |-> 0,
                          viewChangePhase   |-> IDLE,
                          viewChangeSent    |-> FALSE,
                          viewDataSent      |-> FALSE,
                          viewChangeQuorum  |-> [v \in Nat |-> {}],
                          viewDataQuorum    |-> [v \in Nat |-> {}],
                          lastProposal      |-> [s \in Nat |-> Nil]
                        ]
                       ]
    /\ messages = {}
    /\ requests = {}
    /\ decidedProposals = [s \in Nat |-> Nil]

(* -- Actions -- *)

(*
  Preprepare Phase: Leader assembles a batch of client requests into a proposal
  and broadcasts a Preprepare message to all replicas.
*)
Preprepare(self) ==
    /\ self = getLeaderID(replicaState[self].view)
    /\ replicaState[self].viewChangePhase = IDLE
    /\ replicaState[self].seq = currentSequence (* Leader proposes for the next sequence after the highest proposed one *)
    /\ replicaState[self].phase[currentSequence + 1] = IDLE (* Expecting next sequence to be IDLE *)
    /\ \E reqs \in SUBSET requests :
        LET newSeq == currentSequence + 1
            newProposal == [metadata |-> [view |-> replicaState[self].view, seq |-> newSeq], batch |-> reqs]
            preprepareMsg == [type |-> "Preprepare", view |-> replicaState[self].view, seq |-> newSeq, proposal |-> newProposal]
        IN
            /\ messages' = messages \cup {[sender |-> self, receiver |-> r, content |-> preprepareMsg] : r \in Nodes \ {self}}
            /\ replicaState' = [replicaState EXCEPT ![self].phase[newSeq] = PREPARED,
                                                    ![self].seq = newSeq,
                                                    ![self].lastProposal[newSeq] = newProposal]
            /\ requests' = requests \ reqs
            /\ currentSequence' = newSeq (* Update global highest proposed sequence *)
            /\ UNCHANGED <<currentView, decidedProposals>>

(*
  Prepare Phase: Non-leader replica receives the Preprepare, validates it,
  makes sure it is in the right view, and broadcasts a Prepare message.
*)
Prepare(self) ==
    /\ self /= getLeaderID(replicaState[self].view)
    /\ replicaState[self].viewChangePhase = IDLE
    /\ \E sender_pp \in Nodes, preprepareMsg \in PreprepareMsgType :
        /\ preprepareMsg.type = "Preprepare"
        /\ LET received_pp_msg == [sender |-> sender_pp, receiver |-> self, content |-> preprepareMsg] IN
            /\ received_pp_msg \in messages
            /\ preprepareMsg.view = replicaState[self].view
            /\ preprepareMsg.seq = replicaState[self].seq + 1 (* Expecting next sequence *)
            /\ replicaState[self].phase[preprepareMsg.seq] = IDLE
            LET newSeq == preprepareMsg.seq
                prepareMsg == [type |-> "Prepare", view |-> preprepareMsg.view, seq |-> newSeq, proposalHash |-> preprepareMsg.proposal]
            IN
                /\ messages' = (messages \ {received_pp_msg}) \cup {[sender |-> self, receiver |-> r, content |-> prepareMsg] : r \in Nodes \ {self}}
                /\ replicaState' = [replicaState EXCEPT ![self].phase[newSeq] = PREPARED,
                                                        ![self].seq = newSeq,
                                                        ![self].lastProposal[newSeq] = preprepareMsg.proposal]
                /\ UNCHANGED <<currentView, currentSequence, requests, decidedProposals>>

(*
  Commit Phase: If a replica collects a quorum of Prepare messages (2f+1),
  then it broadcasts a Commit message.
*)
Commit(self) ==
    /\ replicaState[self].viewChangePhase = IDLE
    /\ \E sender_p \in Nodes, prepareMsg \in PrepareMsgType :
        /\ prepareMsg.type = "Prepare"
        /\ LET received_p_msg == [sender |-> sender_p, receiver |-> self, content |-> prepareMsg] IN
            /\ received_p_msg \in messages
            /\ prepareMsg.view = replicaState[self].view
            /\ replicaState[self].phase[prepareMsg.seq] = PREPARED
            LET newSeq == prepareMsg.seq
                currentPreparedMsgs == replicaState[self].preparedMessages[newSeq]
                updatedPreparedMsgs == currentPreparedMsgs \cup {<<sender_p, prepareMsg>>}
                commitMsg == [type |-> "Commit", view |-> prepareMsg.view, seq |-> newSeq, proposalHash |-> prepareMsg.proposalHash]
            IN
                /\ IsQuorum({s \in Nodes : \E m \in updatedPreparedMsgs : s = m[1]})
                /\ messages' = (messages \ {received_p_msg}) \cup {[sender |-> self, receiver |-> r, content |-> commitMsg] : r \in Nodes \ {self}}
                /\ replicaState' = [replicaState EXCEPT ![self].phase[newSeq] = COMMITTED,
                                                        ![self].preparedMessages[newSeq] = updatedPreparedMsgs]
                /\ UNCHANGED <<currentView, currentSequence, requests, decidedProposals>>

(*
  Decision: If a replica collects a quorum of Commit messages (2f+1),
  it delivers the decided proposal to the application.
*)
Decide(self) ==
    /\ replicaState[self].viewChangePhase = IDLE
    /\ \E sender_c \in Nodes, commitMsg \in CommitMsgType :
        /\ commitMsg.type = "Commit"
        /\ LET received_c_msg == [sender |-> sender_c, receiver |-> self, content |-> commitMsg] IN
            /\ received_c_msg \in messages
            /\ commitMsg.view = replicaState[self].view
            /\ replicaState[self].phase[commitMsg.seq] = COMMITTED
            /\ replicaState[self].lastDecidedSeq < commitMsg.seq (* Only decide if it's a new decision *)
            LET newSeq == commitMsg.seq
                currentCommitMsgs == replicaState[self].commitMessages[newSeq]
                updatedCommitMsgs == currentCommitMsgs \cup {<<sender_c, commitMsg>>}
                decidedProposal == replicaState[self].lastProposal[newSeq]
            IN
                /\ IsQuorum({s \in Nodes : \E m \in updatedCommitMsgs : s = m[1]})
                /\ messages' = messages \ {received_c_msg} (* Only receive *)
                /\ decidedProposals' = [decidedProposals EXCEPT ![newSeq] = decidedProposal]
                /\ replicaState' = [replicaState EXCEPT ![self].lastDecidedSeq = newSeq,
                                                        ![self].lastDecidedView = commitMsg.view,
                                                        ![self].commitMessages[newSeq] = updatedCommitMsgs]
                /\ UNCHANGED <<currentView, currentSequence, requests>>

(*
  ViewChange: A replica suspects the current leader (heartbeat timeout or equivocation)
  and sends a ViewChange message to all nodes.
*)
ViewChange(self) ==
    /\ replicaState[self].viewChangePhase = IDLE
    /\ replicaState[self].viewChangeSent = FALSE
    LET nextView == replicaState[self].view + 1
        vcMsg == [type |-> "ViewChange",
                  view |-> nextView,
                  lastDecidedSeq |-> replicaState[self].lastDecidedSeq,
                  lastDecidedView |-> replicaState[self].lastDecidedView,
                  inFlightProposal |-> replicaState[self].lastProposal[replicaState[self].seq] (* The proposal it was working on *)
                 ]
    IN
        /\ messages' = messages \cup {[sender |-> self, receiver |-> r, content |-> vcMsg] : r \in Nodes \ {self}}
        /\ replicaState' = [replicaState EXCEPT ![self].viewChangePhase = VIEW_CHANGE_PHASE,
                                                ![self].viewChangeSent = TRUE]
        /\ UNCHANGED <<currentView, currentSequence, requests, decidedProposals>>

(*
  ViewData: After collecting 2f+1 ViewChange messages, a replica sends a signed
  ViewData message to the next-view leader.
*)
ViewData(self) ==
    /\ replicaState[self].viewChangePhase = VIEW_CHANGE_PHASE
    /\ replicaState[self].viewDataSent = FALSE
    /\ \E sender_vc \in Nodes, vcMsg \in ViewChangeMsgType :
        /\ vcMsg.type = "ViewChange"
        /\ LET received_vc_msg == [sender |-> sender_vc, receiver |-> self, content |-> vcMsg] IN
            /\ received_vc_msg \in messages
            /\ vcMsg.view = replicaState[self].view + 1 (* Expecting ViewChange for next view *)
            LET nextView == vcMsg.view
                currentVCQuorum == replicaState[self].viewChangeQuorum[nextView]
                updatedVCQuorum == currentVCQuorum \cup {<<sender_vc, vcMsg>>}
                newLeader == getLeaderID(nextView)
                vdMsg == [type |-> "ViewData",
                          view |-> nextView,
                          sender |-> self,
                          lastDecidedSeq |-> replicaState[self].lastDecidedSeq,
                          lastDecidedView |-> replicaState[self].lastDecidedView,
                          inFlightProposal |-> replicaState[self].lastProposal[replicaState[self].seq]
                         ]
            IN
                /\ IsQuorum({s \in Nodes : \E m \in updatedVCQuorum : s = m[1]})
                /\ messages' = (messages \ {received_vc_msg}) \cup {[sender |-> self, receiver |-> newLeader, content |-> vdMsg]}
                /\ replicaState' = [replicaState EXCEPT ![self].viewChangePhase = VIEW_DATA_PHASE,
                                                    ![self].viewDataSent = TRUE,
                                                    ![self].viewChangeQuorum[nextView] = updatedVCQuorum]
                /\ UNCHANGED <<currentView, currentSequence, requests, decidedProposals>>

(*
  NewView: If the new leader collects 2f+1 ViewData messages, then it broadcasts
  a NewView message to resume consensus.
*)
NewView(self) ==
    /\ self = getLeaderID(replicaState[self].view + 1) (* Must be the leader of the next view *)
    /\ replicaState[self].viewChangePhase = VIEW_DATA_PHASE
    /\ \E sender_vd \in Nodes, vdMsg \in ViewDataMsgType :
        /\ vdMsg.type = "ViewData"
        /\ LET received_vd_msg == [sender |-> sender_vd, receiver |-> self, content |-> vdMsg] IN
            /\ received_vd_msg \in messages
            /\ vdMsg.view = replicaState[self].view + 1 (* Expecting ViewData for next view *)
            LET nextView == vdMsg.view
                currentVDQuorum == replicaState[self].viewDataQuorum[nextView]
                updatedVDQuorum == currentVDQuorum \cup {<<sender_vd, vdMsg>>}
                allViewDataMsgs == {m[2] : m \in updatedVDQuorum} (* Extract just the messages *)
                allLastDecidedSeqs == {m.lastDecidedSeq : m \in allViewDataMsgs}
                allInFlightProposals == {p \in {vdMsg.inFlightProposal : vdMsg \in allViewDataMsgs} : p /= Nil}

                (* Determine the new proposal sequence and initial proposal for the new view *)
                (* Rule: max(lastDecidedSeq) + 1 from all ViewChange messages *)
                newProposalSequence == Max(allLastDecidedSeqs) + 1
                newDecisionsInView == 0 (* Reset decisions in view for new leader *)

                (* Find the proposal with the highest sequence number among in-flight proposals *)
                chosenProposal ==
                    IF allInFlightProposals /= {}
                    THEN CHOOSE p \in allInFlightProposals :
                             p.metadata.seq = Max({p.metadata.seq : p \in allInFlightProposals})
                    ELSE [metadata |-> [view |-> nextView, seq |-> newProposalSequence], batch |-> {}] (* Empty proposal if no in-flight *)

                newViewMsg == [type |-> "NewView",
                               view |-> nextView,
                               newProposalSequence |-> newProposalSequence,
                               newDecisionsInView |-> newDecisionsInView,
                               proposal |-> chosenProposal
                              ]
            IN
                /\ IsQuorum({s \in Nodes : \E m \in updatedVDQuorum : s = m[1]})
                /\ messages' = (messages \ {received_vd_msg}) \cup {[sender |-> self, receiver |-> r, content |-> newViewMsg] : r \in Nodes \ {self}}
                /\ currentView' = nextView
                /\ currentSequence' = newProposalSequence (* Update global highest proposed sequence *)
                /\ replicaState' = [replicaState EXCEPT ![self].view = nextView,
                                                    ![self].seq = newProposalSequence - 1, (* Leader will propose newProposalSequence *)
                                                    ![self].phase = [s \in Nat |-> IDLE], (* Reset phases *)
                                                    ![self].preparedMessages = [s \in Nat |-> {}],
                                                    ![self].commitMessages = [s \in Nat |-> {}],
                                                    ![self].viewChangePhase = IDLE,
                                                    ![self].viewChangeSent = FALSE,
                                                    ![self].viewDataSent = FALSE,
                                                    ![self].viewChangeQuorum = [v \in Nat |-> {}],
                                                    ![self].viewDataQuorum = [v \in Nat |-> {}],
                                                    ![self].lastProposal[newProposalSequence] = chosenProposal
                                                   ]
                /\ UNCHANGED <<requests, decidedProposals>>

(*
  HandleNewView: Non-leader replica receives a NewView message and updates its state.
*)
HandleNewView(self) ==
    /\ self /= getLeaderID(replicaState[self].view + 1) (* Not the new leader *)
    /\ replicaState[self].viewChangePhase \in {VIEW_CHANGE_PHASE, VIEW_DATA_PHASE}
    /\ \E sender_nv \in Nodes, nvMsg \in NewViewMsgType :
        /\ nvMsg.type = "NewView"
        /\ LET received_nv_msg == [sender |-> sender_nv, receiver |-> self, content |-> nvMsg] IN
            /\ received_nv_msg \in messages
            /\ nvMsg.view = replicaState[self].view + 1 (* Expecting NewView for next view *)
            LET nextView == nvMsg.view
                newProposalSequence == nvMsg.newProposalSequence
                initialProposal == nvMsg.proposal
            IN
                /\ messages' = messages \ {received_nv_msg} (* Only receive *)
                /\ currentView' = nextView
                /\ currentSequence' = newProposalSequence (* Update global highest proposed sequence *)
                /\ replicaState' = [replicaState EXCEPT ![self].view = nextView,
                                                    ![self].seq = newProposalSequence - 1, (* Will expect newProposalSequence *)
                                                    ![self].phase = [s \in Nat |-> IDLE], (* Reset phases *)
                                                    ![self].preparedMessages = [s \in Nat |-> {}],
                                                    ![self].commitMessages = [s \in Nat |-> {}],
                                                    ![self].viewChangePhase = IDLE,
                                                    ![self].viewChangeSent = FALSE,
                                                    ![self].viewDataSent = FALSE,
                                                    ![self].viewChangeQuorum = [v \in Nat |-> {}],
                                                    ![self].viewDataQuorum = [v \in Nat |-> {}],
                                                    ![self].lastProposal[newProposalSequence] = initialProposal
                                                   ]
                /\ UNCHANGED <<requests, decidedProposals>>

(*
  ProcessViewChangeMessage: Non-leader nodes in view change phases process incoming
  ViewChange and ViewData messages to collect quorums.
*)
ProcessViewChangeMessage(self) ==
    /\ replicaState[self].viewChangePhase \in {VIEW_CHANGE_PHASE, VIEW_DATA_PHASE}
    /\ \E sender_vc_vd \in Nodes, msg \in MessageType :
        /\ LET received_msg == [sender |-> sender_vc_vd, receiver |-> self, content |-> msg] IN
            /\ received_msg \in messages
            /\ msg.view = replicaState[self].view + 1 (* Only process messages for the next view *)
            /\ messages' = messages \ {received_msg} (* Always receive the message *)
            /\ replicaState' =
                 CASE msg.type = "ViewChange" ->
                          LET currentVCQuorum == replicaState[self].viewChangeQuorum[msg.view]
                              updatedVCQuorum == currentVCQuorum \cup {<<sender_vc_vd, msg>>}
                          IN
                              [replicaState EXCEPT ![self].viewChangeQuorum[msg.view] = updatedVCQuorum]
                 [] msg.type = "ViewData" ->
                          LET currentVDQuorum == replicaState[self].viewDataQuorum[msg.view]
                              updatedVDQuorum == currentVDQuorum \cup {<<sender_vc_vd, msg>>}
                          IN
                              [replicaState EXCEPT ![self].viewDataQuorum[msg.view] = updatedVDQuorum]
                 [] OTHER -> (* For any other message type, just consume it and don't change replicaState *)
                          replicaState
            /\ UNCHANGED <<currentView, currentSequence, requests, decidedProposals>>

(*
  DiscardMessage: A generic action for a node to receive and discard a message if it's not relevant
  (e.g., old view, or not in the right phase/sequence for a positive action).
*)
DiscardMessage(self) ==
    /\ \E sender_d \in Nodes, msg \in MessageType :
        /\ LET received_d_msg == [sender |-> sender_d, receiver |-> self, content |-> msg] IN
            /\ received_d_msg \in messages
            /\ \/ msg.view < replicaState[self].view (* Message from an old view *)
               \/ (msg.type \in {"Preprepare", "Prepare", "Commit"} /\ replicaState[self].viewChangePhase /= IDLE) (* Normal message during view change *)
               \/ (msg.type \in {"ViewChange", "ViewData", "NewView"} /\ replicaState[self].viewChangePhase = IDLE) (* View change message during normal operation *)
               \/ (msg.type \in {"ViewChange", "ViewData", "NewView"} /\ msg.view /= replicaState[self].view + 1) (* View change message for wrong target view *)
               \/ (msg.type = "Preprepare" /\ self /= getLeaderID(msg.view) /\ msg.seq /= replicaState[self].seq + 1) (* Non-leader Preprepare for wrong seq *)
        /\ messages' = messages \ {received_d_msg}
        /\ UNCHANGED <<currentView, currentSequence, replicaState, requests, decidedProposals>>

(*
  AddRequest: A client submits a request to the system.
  This is simplified as per requirements.
*)
AddRequest ==
    /\ \E req \in RequestType :
        /\ req \notin requests
        /\ requests' = requests \cup {req}
    /\ UNCHANGED <<currentView, currentSequence, replicaState, messages, decidedProposals>>

(*
  Stuttering: Nothing happens.
*)
Stutter ==
    UNCHANGED <<currentView, currentSequence, replicaState, messages, requests, decidedProposals>>

(* -- Next State -- *)
Next ==
    \/ \E self \in Nodes :
        \/ Preprepare(self)
        \/ Prepare(self)
        \/ Commit(self)
        \/ Decide(self)
        \/ ViewChange(self)
        \/ ViewData(self)
        \/ NewView(self)
        \/ HandleNewView(self)
        \/ ProcessViewChangeMessage(self)
        \/ DiscardMessage(self)
    \/ AddRequest
    \/ Stutter

(* -- Specification -- *)
(*
  Fairness assumptions are crucial for liveness properties.
  WF_vars(A) means that if action A is continuously enabled, it eventually occurs.
  We apply this to all actions that involve a specific node (self) to ensure progress.
  AddRequest and Stutter are not tied to a specific node, so they don't need WF_vars.
*)
Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(\E self \in Nodes : Preprepare(self))
    /\ WF_vars(\E self \in Nodes : Prepare(self))
    /\ WF_vars(\E self \in Nodes : Commit(self))
    /\ WF_vars(\E self \in Nodes : Decide(self))
    /\ WF_vars(\E self \in Nodes : ViewChange(self))
    /\ WF_vars(\E self \in Nodes : ViewData(self))
    /\ WF_vars(\E self \in Nodes : NewView(self))
    /\ WF_vars(\E self \in Nodes : HandleNewView(self))
    /\ WF_vars(\E self \in Nodes : ProcessViewChangeMessage(self))
    /\ WF_vars(\E self \in Nodes : DiscardMessage(self))
    /\ WF_vars(AddRequest)

vars == <<currentView, currentSequence, replicaState, messages, requests, decidedProposals>>

====
```
```cfg
SPECIFICATION Spec

CONSTANTS
    Nodes = {1, 2, 3, 4}
    f = 1
    Nil = "Nil"
    IDLE = "IDLE"
    PREPARED = "PREPARED"
    COMMITTED = "COMMITTED"
    VIEW_CHANGE_PHASE = "VIEW_CHANGE_PHASE"
    VIEW_DATA_PHASE = "VIEW_DATA_PHASE"
    NEW_VIEW_PHASE = "NEW_VIEW_PHASE"

(*
  For RequestType and ProposalType, TLC needs concrete finite values.
  We define a small set of example requests for model checking.
*)
RequestType = {"req1", "req2"}
```