--------------------------------------- MODULE coordinationengine --------------------------------------

EXTENDS     FiniteSets, Sequences, Naturals, TLC

----------------------------------------------------------------------------------------

(* The implementation of the CE should generate a sequence of agreements from submitted *)
(* proposals. *)

----------------------------------------------------------------------------------------


VARIABLE    proposals,                         \* The set of proposals submitted to
                                               \* the coordination engine and not yet
                                               \* agreed.
            rejections,                        \* The set of rejection records.
            usedIds,                           \* The set of used proposal identities.
            currentGsn,                        \* The current global sequence number
                                               \* of the coordination engine.
            agreements                         \* The sequence of agreements 
                                               \* produced by the coordination
                                               \* engine.


CONSTANTS   Proposer,                          \* The set of all proposers.
            ProposalId,                        \* The set of all proposal
                                               \* identities that can be used.
            Reason,                            \* The set of all reasons a value can
                                               \* be rejected.                                               
            Value,                             \* The set of all values that can be
                                               \* proposed.
            MaxOutstandingProposals            \* The maximum number of 
                                               \* outstanding (yet to be agreed) 
                                               \* proposals the coordination engine 
                                               \* can have.


ASSUME (MaxOutstandingProposals \in Nat) /\ (MaxOutstandingProposals > 0)

             
----------------------------------------------------------------------------------------
(* Tuple of all variables.  *)


vars == << proposals, rejections, usedIds, currentGsn, agreements >>  


----------------------------------------------------------------------------------------
(* Records. *)


Proposal == [ type: "Proposal",
              proposer: Proposer,
              proposalId: ProposalId,
              value: Value ]

Agreement == [ type: "Agreement",
               proposer: Proposer,
               proposalId: ProposalId,
               value: Value,
               agreementGsn: Nat ]   

Rejection == [ type: "Rejection",
               proposer: Proposer,
               value: Value,
               reason: Reason ]


----------------------------------------------------------------------------------------
(* A function to return a proposal identity that hasn't been used before. This ensures each *) 
(* proposal has a unique identity. Also provided is a function to tell us if there are any proposal *)
(* identities remaining, which is used as a constraint when model checking. *)


NewId == CHOOSE id \in ProposalId : id \notin usedIds


ProposalIdAvailable == Cardinality( usedIds ) < Cardinality( ProposalId )


----------------------------------------------------------------------------------------
(* If the CE is accepting values, the proposal is submitted else the rejection is recorded. *)


Reject( p, v ) == LET r == [ type |-> "Rejection",
                               proposer |-> p,
                               value |-> v,
                               reason |-> "NotAcceptingProposals" ]
                  IN /\ rejections' = rejections \cup { r }
                     /\ UNCHANGED << proposals, usedIds, currentGsn, agreements >>


SubmitProposal( p ) == /\ proposals' = proposals \cup { p }
                       /\ usedIds' = usedIds \cup { p.proposalId }
                       /\ UNCHANGED << rejections, currentGsn, agreements >>


(* There could be many reasons why proposals cannot be accepted, this is one example. *)

AcceptingProposals == Cardinality( proposals ) < MaxOutstandingProposals  
                                                            


SubmitValue( p, v ) == IF AcceptingProposals 
                       THEN SubmitProposal( [ type |-> "Proposal",
                                            proposer |-> p,
                                            proposalId |-> NewId,
                                            value |-> v ] ) 
                       ELSE Reject( p, v )


----------------------------------------------------------------------------------------
(* To add an agreement to the sequence the proposal must be agreed. How a proposal is agreed is *)
(* dependent on the consensus/coordination algoritm implemented by the CE. *)


AgreeProposal( p ) == LET a == [ type |-> "Agreement",
                                 proposer |-> p.proposer,
                                 proposalId |-> p.proposalId,
                                 value |-> p.value,
                                 agreementGsn |-> currentGsn + 1 ]
                      IN /\ proposals' = proposals \ { p }
                         /\ currentGsn' = currentGsn + 1
                         /\ agreements' = Append(agreements, a)
                         /\ UNCHANGED << usedIds, rejections >>


EmitAgreement ==  \E p \in proposals: AgreeProposal( p )


----------------------------------------------------------------------------------------
(* Type invariants. *)


TypeInvariant == /\ \A id \in usedIds : id \in ProposalId
                 /\ \A p \in proposals : p.type = "Proposal"
                 /\ \A r \in rejections : r.type = "Rejection" /\ r.reason \in Reason
                 /\ Cardinality( proposals ) \leq MaxOutstandingProposals
                 /\ currentGsn \in Nat                       


----------------------------------------------------------------------------------------
(* All agreed values must be an agreement, the proposalId must be in the set of usedIds (i.e., all *)
(* agreements must be the result of a submitted proposal), the sequence number of each agreement *)
(* must be in the correct position in the sequence. *)


CheckAgreement( a, i ) == /\ a.type = "Agreement"
                          /\ a.proposalId \in usedIds
                          /\ a.agreementGsn = i


CheckAgreementSequence[ l \in Nat ] == 
                           IF l = 0
                           THEN TRUE
                           ELSE LET i == l - 1 
                                IN /\ CheckAgreement( agreements[ i ], l )
                                   /\ CheckAgreementSequence[ i ]


Safety == LET l == Len( agreements )    
          IN CheckAgreementSequence[ l ]


----------------------------------------------------------------------------------------
(* All submitted proposals should eventually be agreed.                               *)


Liveness == <>( proposals = {} )


----------------------------------------------------------------------------------------
(* The next state is found through either submitting a value or emitting an agreement.*)


Next == \/ \E p \in Proposer : (\E v \in Value : SubmitValue( p, v ))
        \/ EmitAgreement


----------------------------------------------------------------------------------------
(* Initial state.                                                                     *)


Init == /\ proposals  = {}                     \* No proposals have been made.  
        /\ rejections = {}                     \* Nothing has been rejected.
        /\ usedIds = {}                        \* No proposal ids have been used.
        /\ currentGsn = 0                      \* Global sequence number is zero.
        /\ agreements = <<>>                   \* No agreements have been output.                              


---------------------------------------------------------------------------------------- 
CESpec == /\ Init 
          /\ [][Next]_vars 
          /\ Safety 
          /\ Liveness
---------------------------------------------------------------------------------------- 
THEOREM CESpec => []TypeInvariant
========================================================================================