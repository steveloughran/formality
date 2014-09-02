---------------------------- MODULE yarnregistry ----------------------------

EXTENDS FiniteSets, Sequences, Naturals, TLC


(* a path element is all chars excluding "/" *)

CONSTANTS
            PathChars,  \* the set of valid characters in a path 
            Paths,      \* the set of all possible valid paths 
            Data        \* the set of all possible sequences of bytes



(* all paths in the system *)
VARIABLE registry

(*

 Path operations

*)

(* parent is defined for non empty sequences *)

parent(p) == SubSeq(p, 1, Len(p)-1)

isParent(p, c) == p = parent(c) 



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

(* the set of all children of a path in the registry *)

children(R, p) == \A e \in R: isParent(p, e.path)

(*

For validity, all entries must match the following criteria

* there can be at most one entry with a given path in the set
* their path is either [] or a parent path which must also be found in the registry
* no entry may have a parent that is ephemeral

 *)

validRegistry(R) ==
        /\ \A e \in R:  Cardinality(lookup(R, e.path)) = 1 
        /\ \A e \in R:  (isRoot(e) \/  ~isEphemeral(Head(parentEntry(R, e.path)) ) )

(*
The initial state of a registry has the root entry.
*)

InitialRegistry == {
  [ path |-> <<>>, ephemeral |-> FALSE, data |-> <<>> ]
}

(* Deletion is set difference on any existing entries *)

simpleDelete(R, p) ==
    /\ children(R, p) = {}
    /\ R' = R \ lookup(R, p)



=============================================================================

  
 




=============================================================================
=============================================================================

