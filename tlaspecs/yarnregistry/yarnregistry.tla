---------------------------- MODULE yarnregistry ----------------------------


EXTENDS Sequences

(* a path element is all chars excluding "/" *)

CONSTANTS
            PathChars,  \* the set of valid characters in a path 
            Paths,      \* the set of all possible valid paths 
            Data        \* the set of all possible sequences of bytes



(* all paths in the system *)
VARIABLE registryPaths

PathCharInvariant == PathChars \subseteq STRING 

PathInvariant == \A p \in registryPaths:  \A pe \in p : pe \in PathChars

(*
isRoot[P] == p = []
*) 
(* parent(p, q) == *) 

=============================================================================

(*
An Entry is defined as a path, an ephemerality flag, and  the actual data which it contains.

By including the path in an entry, we avoid having to define some function
mapping Path -> entry. Instead a registry can be defined as a set of RegistryEntries
matching the validity critera.

*)

RegistryEntry == [
        path: Paths,                \* The path to the entry
        ephemeral: BOOLEAN,         \* A flag to indicate when the entry is ephemeral
        data: Data]                 \* the data in the entry


(***************************************************************************
For validity, all entries must match the following criteria

* there can be at most one entry with a given path in the set
* their path is either [] or a parent path which must also be found in the registry
* no entry may have a parent that is ephemeral

 ***************************************************************************)

=============================================================================
=============================================================================
\* Modification History
\* Last modified Mon Sep 01 18:50:01 BST 2014 by stevel
\* Created Sun Aug 31 14:54:47 BST 2014 by stevel
