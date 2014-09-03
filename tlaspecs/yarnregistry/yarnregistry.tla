---------------------------- MODULE yarnregistry ----------------------------



(*

This defines the YARN registry in terms of operations on sets of records.

Every registry entry is represented as a record containing both the path and the data.

It assumes that

1. operations on this set are immediate. 
2. selection operations (such as \A and \E are atomic) 
3. changes are immediately visible to all other users of the registry. 
4. (3) This clearly implies that changes are visible in the sequence in which they happen.

A Zookeeper-based registry does not meet all those assumptions

1. changes may take time to propagate across the ZK quorum, hence changes cannot be considered immediate
from the perspective of other registry clients. (assumptions (1) and (3)).

2. Selection operations may not be atomic. (assumption (2)).

Operations will still happen in the order executed by a client (4)

A stricter definition would try to state that all operations are eventually true excluding other changes
happening during a sequence of action. This is left as an excercise for the reader.

*)


EXTENDS FiniteSets, Sequences, Naturals, TLC


(* a path element is all chars excluding "/" *)

CONSTANTS
            PathChars,   \* the set of valid characters in a path 
            Paths,       \* the set of all possible valid paths 
            Data,        \* the set of all possible sequences of bytes
            Address,     \* the set of all possible address n-tuples
            Addresses,   \* the set of all possible address instances
            Endpoints ,    \* the set of all possible endpoints
            PersistPolicies,     \* the subset of Naturals covering persistence policies
            ServiceRecords,   \* all service records
            Registries,     \* the set of all possile registries 
            PutActions,     \* all possible put actions
            DeleteActions \* all possible delete actions



(* the registry*)
VARIABLE registry

(* Sequence of actions to apply to the registry *)
VARIABLE actions

----------------------------------------------------------------------------------------
(* Tuple of all variables.  *)


vars == << registry, actions >>  



----------------------------------------------------------------------------------------
(* Type invariants. *)


TypeInvariant ==
    /\ \A r \in registry: r \in ServiceRecords
    /\ \A a \in actions: ((a \in PutActions /\ a.type="put") \/ (a \in DeleteActions /\ a.type="delete"))



----------------------------------------------------------------------------------------

(* Records *)


(*

An Entry is defined as a path, an ephemerality flag, and the actual
data which it contains.

By including the path in an entry, we avoid having to define some
function mapping Path -> entry.  Instead a registry can be defined as a
set of RegistryEntries matching the validity critera.

*)

RegistryEntry == [
        path: Paths,                \* The path to the entry
        ephemeral: BOOLEAN,         \* A flag to indicate when the entry is ephemeral
        data: Data]                 \* the data in the entry


Endpoint == [
    api: STRING,
    addresses: Addresses
]


ServiceRecord == [
    id: STRING,
    persistence: PersistPolicies,
    description: STRING,
    endpoints: Endpoints
]

putAction == [
    type: "put",
    record: ServiceRecord
]

deleteAction == [
    type: "delete",
    path: STRING,
    recursive: BOOLEAN
]





(* define some marshalling operation ServiceRecord -> data *)

\* marshall(s)



----------------------------------------------------------------------------------------

(*

 Path operations

*)

(* parent is defined for non empty sequences *)

parent(p) == SubSeq(p, 1, Len(p)-1)

isParent(p, c) == p = parent(c) 

----------------------------------------------------------------------------------------
(*
Registry Operations
*)
(* 
Lookup all entries in a registry with a matching path
*)
lookup(Registry, path) == \A entry \in Registry: entry.path = path


(*
A path exists in the registry iff there is an entry with that path
*)

exists(Registry, path) == lookup(Registry, path) /= {}

(* parent entry, or an empty set if there is none *)
parentEntry(Registry, path) == lookup(Registry, parent(path)) 

(* the root entry *)
isRoot(e) == e.path = <<>>


(* ephemeral *)

isEphemeral(e) == e.ephemeral = TRUE

(* A path p is an ancestor of another path  d if they are different, and the path d
   starts with path p *) 
   
isAncestorOf(p, d) ==
    /\ p /= d 
    /\ \E k : SubSeq(d, 0, k) = p

(* the set of all children of a path in the registry *)

children(R, p) == \A c \in R: isParent(p, c.path)

(* a path has children if the children() function does not return the empty set *)
hasChildren(R, p) == children(R, p) /= {}

(* Descendant: a child of a path or a descendant of a child of a path *)

descendants(R, p) == \A c \in R: isAncestorOf(p, c.path)



(*

For validity, all entries must match the following criteria

* there can be at most one entry with a given path in the set
* their path is either <<>> or a parent path which must also be found in the registry
* no entry may have a parent that is ephemeral

 *)

validRegistry(R) ==
        /\ \E e \in R: isRoot(e)
        /\ \A e \in R:  Cardinality(lookup(R, e.path)) = 1 
        /\ \A e \in R:  (isRoot(e) \/  ~isEphemeral(Head(parentEntry(R, e.path)) ) )

(* Deletion is set difference on any existing entries *)

simpleDelete(R, p) ==
    /\ ~isRoot(p)
    /\ children(R, p) = {}
    /\ R' = R \ lookup(R, p)

(* recursive delete: neither the path or its descendants exists in the new registry *)

recursiveDelete(R, p) ==
    /\ ~isRoot(p)
    /\ R' = R \ ( lookup(R, p) \union descendants(R, p))

(* Delete operation *)

delete(R, p, recursive) == 
    IF recursive  THEN recursiveDelete(R, p) ELSE simpleDelete(R, p) 


(*
 An entry can be put into the registry iff 
 -its parent is present or it is the root entry
 -if it is marked as ephemeral, there are no child entries in the registry
 -if it is marked as ephemeral, it is not a change to the root entry

*)
canPut(R, e) == 
    /\   isRoot(e) \/ exists(R, parent(e.path)) 
    /\ ~(isEphemeral(e) /\  hasChildren(R, e.path))
    /\ ~(isEphemeral(e) /\  isRoot(e))

(* put adds/replaces an entry if permitted *)

 put(R, e) ==
    /\ canPut(R, e)
    /\ R' = (R \ lookup(R, e.path)) \union e
    
 
applyAction(R, a) == 
    /\ (a \in PutActions /\ put(R, a.record) )
    /\ (a \in DeleteActions /\ delete(R, a.path, a.recursive) )
 
 
applyFirstAction(R, a) ==
    /\ actions /= <<>>
    /\ applyAction(R, Head(a))
    /\ actions' = Tail(a)
    

Next == applyFirstAction(registry, actions)    
 
 (* All submitted actions should eventually be applied. *)


Liveness == <>( actions = <<>> )
 
 
(*
The initial state of a registry has the root entry.
*)

InitialRegistry == registry = {
  [ path |-> <<>>, ephemeral |-> FALSE, data |-> <<>> ]
}

ValidRegistryState == validRegistry(registry)




InitialState ==
    /\ InitialRegistry
    /\ ValidRegistryState
    /\ actions = <<>>


RegistrySpec ==
    /\ InitialState
    /\ [][Next]_vars
    /\ Liveness    



=============================================================================

(* Theorem: For all operations from that initial state, the registry state is still valid *)
THEOREM InitialState ==> [] ValidRegistryState

(* Theorem: for all operations from that initial state, the type invariants hold *)
THEOREM InitialState ==> [] TypeInvariant

=============================================================================

