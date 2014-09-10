---------------------------- MODULE yarnregistry ----------------------------

EXTENDS FiniteSets, Sequences, Naturals, TLC


(*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(*

============================================================================

This defines the YARN registry in terms of operations on sets of records.

Every registry entry is represented as a record containing both the path and the data.

It assumes that

1. operations on this set are immediate. 
2. selection operations (such as \A and \E are atomic) 
3. changes are immediately visible to all other users of the registry. 
4. This clearly implies that changes are visible in the sequence in which they happen.

A Zookeeper-based registry does not meet all those assumptions

1. changes may take time to propagate across the ZK quorum, hence changes cannot be considered immediate
from the perspective of other registry clients. (assumptions (1) and (3)).

2. Selection operations may not be atomic. (assumption (2)).

Operations will still happen in the order received by the elected ZK master

A stricter definition would try to state that all operations are eventually true excluding other changes
happening during a sequence of action. This is left as an excercise for the reader.

*)



CONSTANTS
    PathChars,     \* the set of valid characters in a path 
    Paths,         \* the set of all possible valid paths 
    Data,          \* the set of all possible sequences of bytes
    Address,       \* the set of all possible address n-tuples
    Addresses,     \* the set of all possible address instances
    Endpoints ,    \* the set of all possible endpoints
    PersistPolicies,\* the set of persistence policies
    ServiceRecords, \* all service records
    Registries,     \* the set of all possile registries 
    PutActions,     \* all possible put actions
    DeleteActions,  \* all possible delete actions
    PurgeActions,   \* all possible purge actions
    MkdirActions    \* all possible mkdir actions



(* the registry*)
VARIABLE registry

(* Sequence of actions to apply to the registry *)
VARIABLE actions

----------------------------------------------------------------------------------------
(* Tuple of all variables.  *)


vars == << registry, actions >>  


----------------------------------------------------------------------------------------




(* Persistence policy *)
PersistPolicySet == {
    "MANUAL",              \* persists until manually removed 
    "CLUSTER-RESTART",      \* persists until the cluster is restarted
    "APPLICATION",          \* persists until the application finishes
    "APPLICATION-ATTEMPT",  \* persists until the application attempt finishes
    "CONTAINER",            \* persists until the container finishes 
    "EPHEMERAL"            \* the record is ephemeral
    }

(* Type invariants. *)
TypeInvariant ==
    /\ \A p \in PersistPolicies: p \in PersistPolicySet
    


----------------------------------------------------------------------------------------



(*

An Entry is defined as a path, an ephemerality flag, and the actual
data which it contains.

By including the path in an entry, we avoid having to define some
function mapping Path -> entry.  Instead a registry can be defined as a
set of RegistryEntries matching the validity critera.

*)

RegistryEntry == [
    \* The path to the entry
    path: Paths, 

    \* A flag to indicate when the entry is ephemeral
    ephemeral: BOOLEAN, 

    \* the data in the entry
    data: Data
    ]
    

(*
    An endpoint in a service record
*)
Endpoint == [
    \* API of the endpoint: some identifier
    api: STRING,
    \* A list of address n-tuples
    addresses: Addresses
]

(*
    A service record
*)
ServiceRecord == [
    \* ID -used when applying the persistence policy
    id: STRING,             
    \* the persistence policy
    persistence: PersistPolicySet,
    
    \*A description
    description: STRING,
    
    \* A set of endpoints
    external: Endpoints,
    
    \* Endpoints intended for use internally
    internal: Endpoints
]


----------------------------------------------------------------------------------------

(* Action Records *)

putAction == [
    type: "put",
    record: ServiceRecord
]

deleteAction == [
    type: "delete",
    path: STRING,
    recursive: BOOLEAN
]

purgeAction == [
    type: "purge",
    path: STRING,
    persistence: PersistPolicySet
]

mkDirAction == [
    type: "mkdir",
    path: STRING,
    parents: BOOLEAN
]




----------------------------------------------------------------------------------------

(*

 Path operations

*)

(* parent is defined for non empty sequences *)

parent(path) == SubSeq(path, 1, Len(path)-1)

isParent(path, c) == path = parent(c) 

----------------------------------------------------------------------------------------
(*
Registry Access Operations
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

isRootPath(path) == path = <<>>

(* the root entry *)
isRootEntry(entry) == entry.path = <<>>


(* ephemeral *)

isEphemeral(entry) == entry.ephemeral

(* A path p is an ancestor of another path d if they are different, and the path d
   starts with path p *) 
   
isAncestorOf(path, d) ==
    /\ path /= d 
    /\ \E k : SubSeq(d, 0, k) = path


ancestorPathOf(path) == 
    \A a \in Paths: isAncestorOf(a, path)

(* the set of all children of a path in the registry *)

children(R, path) == \A c \in R: isParent(path, c.path)

(* a path has children if the children() function does not return the empty set *)
hasChildren(R, path) == children(R, path) /= {}

(* Descendant: a child of a path or a descendant of a child of a path *)

descendants(R, path) == \A e \in R: isAncestorOf(path, e.path)

ancestors(R, path) == \A e \in R: isAncestorOf(e.path, path)

(*
The set of entries that are a path and its descendants
*)
pathAndDescendants(R, path) ==
    \/ \A e \in R: isAncestorOf(path, e.path)
    \/ lookup(R, path) 


(*

For validity, all entries must match the following criteria

 *)

validRegistry(R) ==
        \* there can be at most one entry for a path.    
        /\ \A e \in R: Cardinality(lookup(R, e.path)) = 1

        \* There's at least one root entry 
        /\ \E e \in R: isRootEntry(e)                   
        
        \* no root entry may be ephemeral             
        /\ \E e \in R: isRootEntry(e) => ~e.ephemeral
                
         \* an entry must be the root entry or have a parent entry
        /\ \A e \in R: isRootEntry(e) \/ exists(R, parent(e.path))
          
        \* If the entry has data, it must be a service record
        /\ \A e \in R: (e.data = << >> \/ e.data \in ServiceRecords) 
        
        \* if an entry is not root, it cannot have an ephemeral parent
        /\ \A e \in R: (isRootEntry(e) \/  ~isEphemeral(Head(parentEntry(R, e.path)) ) ) 


----------------------------------------------------------------------------------------
(*
    Registry Manipulation
*)

(*
 An entry can be put into the registry iff 
 -its parent is present or it is the root entry
 -if it is marked as ephemeral, there are no child entries in the registry
 -if it is marked as ephemeral, it is not a change to the root entry

*)
canPut(R, e) == 
    /\  isRootEntry(e) \/ (\A p \in parentEntry(R, e.path): ~p.ephemeral )  
    /\ (isEphemeral(e) => ~hasChildren(R, e.path))
    /\ (isEphemeral(e) => ~isRootEntry(e))

(* put adds/replaces an entry if permitted *)

put(R, e) ==
    /\ canPut(R, e)
    /\ R' = (R \ lookup(R, e.path)) \union e
    

(*
    mkdir() adds a new empty entry where there was none before, iff
    -the parent exists
    -it meets the requirement for being "put"
*)

mkdirSimple(R, path) ==
    LET record == [ path |-> path, ephemeral |-> FALSE, data |-> <<>>  ]
    IN  \/ exists(R, path)
        \/ (exists(R, parent(path))  /\ canPut(R, record) /\ (R' = R \union record ))


(*
For all parents, the mkdirSimple criteria must apply.
This could be defined recursively, except what is not being defined here is a set. 

It declares that the mkdirSimple state applies to the path and all its parents in the set R'

*)
mkdirWithParents(R, path) ==
    /\ \A p2 \in ancestors(R, path) : mkdirSimple(R, p2)
    /\ mkdirSimple(R, path)
    

mkdir(R, path, recursive) ==
   IF recursive THEN mkdirWithParents(R, path) ELSE mkdirSimple(R, path)
  
(* Deletion is set difference on any existing entries *)

simpleDelete(R, path) ==
    /\ ~isRootPath(path)
    /\ children(R, path) = {}
    /\ R' = R \ lookup(R, path)

(* recursive delete: neither the path or its descendants exists in the new registry *)

(* TODO: Define the special case of root delete: the path remains but nothing else *)

recursiveDelete(R, path) ==
    /\ ~isRootPath(path)
    /\ R' = R \ ( lookup(R, path) \union descendants(R, path))


(* Delete operation which chooses the recursiveness policy based on an argument*)

delete(R, path, recursive) == 
    IF recursive THEN recursiveDelete(R, path) ELSE simpleDelete(R, path) 

   
(* 
Purge ensures that all entries under a path with the matching ID and policy are not there
afterwards
*)

purge(R, path, id, persistence) == 
    /\ (persistence \in PersistPolicySet)
    /\ \A p2 \in pathAndDescendants(R, path) :
         (p2.id = id /\ p2.persistence = persistence) => recursiveDelete(R, p2.path) 

(*
Resolve() resolves the record at a path or fails.

It relies on the fact that if the cardinality of a set is 1, then the CHOOSE operator
is guaranteed to return the single entry of that set, iff the choice predicate holds. Using
a predicate of TRUE, it always succeeds, so this function selects the sole entry of the lookup operation.
*)
resolveRecord(R, path) ==
    LET l == lookup(R, path) IN
        /\ Cardinality(l) = 1
        /\ CHOOSE e \in l : TRUE


(*
 The specific action of putting an entry into a record includes validating the record
*)

validRecordToPut(path, ephemeral, record) ==
        \* all records declared ephemeral must be put
        \* as an ephemeral node -and vice versa
    /\ (ephemeral <=> record.persistence = "EPHEMERAL")
    
        \* The root entry must have manual persistence  
    /\ (isRootPath(path) => record.persistence = "MANUAL")


(* 
 putting a service record involves validating it then putting it in the registry
 marshalled as the data in the entry
 *)
putRecord(R, path, ephemeral, record) ==
    /\ validRecordToPut(path, ephemeral, record)
    /\ put(R, [path |-> path, ephemeral |-> ephemeral, data |-> record])


----------------------------------------------------------------------------------------

 

(*
    The action queue can only contain one of the sets of action types, and
    by giving each a unique name, those sets are guaranteed to be disjoint
*) 
 QueueInvariant ==   
    /\ \A a \in actions: 
        \/ (a \in PutActions /\ a.type="put") 
        \/ (a \in DeleteActions /\ a.type="delete")
        \/ (a \in PurgeActions /\ a.type="purge")
        \/ (a \in MkdirActions /\ a.type="mkdir")



(*
    Applying queued actions
*)
 
applyAction(R, a) == 
    \/ (a \in PutActions /\ putRecord(R, a.path, a.ephemeral, a.record) )
    \/ (a \in MkdirActions /\ mkdir(R, a.path, a.recursive) )
    \/ (a \in DeleteActions /\ delete(R, a.path, a.recursive) )
    \/ (a \in PurgeActions /\ purge(R, a.path, a.id, a.persistence))
 
 
(*
    Apply the first action in a list and then update the actions
*)
applyFirstAction(R, a) ==
    /\ actions /= <<>>
    /\ applyAction(R, Head(a))
    /\ actions' = Tail(a)
    

Next == applyFirstAction(registry, actions)    
 
(*
All submitted actions must eventually be applied.
*)


Liveness == <>( actions = <<>> )
 
 
(*
The initial state of a registry has the root entry.
*)

InitialRegistry == registry = {
  [ path |-> <<>>, ephemeral |-> FALSE, data |-> <<>> ]
}


(* 
The valid state of the "registry" variable is defined as
Via the validRegistry predicate
*)

ValidRegistryState == validRegistry(registry)



(*
The initial state of the system
*)
InitialState ==
    /\ InitialRegistry
    /\ ValidRegistryState
    /\ actions = <<>>


(*
The registry has an initial state, the series of state changes driven by the actions,
and the requirement that it does act on those actions.
*)
RegistrySpec ==
    /\ InitialState
    /\ [][Next]_vars
    /\ Liveness    


----------------------------------------------------------------------------------------

(*
Theorem: For all operations from that initial state, the registry state is still valid 
*)
THEOREM InitialState => [] ValidRegistryState

(* 
Theorem: for all operations from that initial state, the type invariants hold 
*)
THEOREM InitialState => [] TypeInvariant

THEOREM InitialState => [] QueueInvariant

=============================================================================

