---------------------------- MODULE objectstore ----------------------------


EXTENDS FiniteSets, Sequences, Nats, TLC


(*
============================================================================
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
============================================================================
 *)

(*

============================================================================

This specification defines

1. A model of an object store: an eventually consistent store of data and metadata,
one without any notion of a "directory hierarchy". It is intended to model
object stores such as Amazon S3 and OpenStack swift, while leaving scope for
optional features which may only be available on other stores.

2. An API for communicating with object stores from Hadoop filesystems. 


3. How the Object Store API must translate into changes in the state of the Object Store
itself. That is: what must an implementation do?




============================================================================

*)

CONSTANTS
    PathChars,     \* the set of valid characters in a path; the alphabet
    Paths,         \* the non-finite set of all possible valid paths
    Data,          \* the non-finite set of all possible sequences of bytes
    MetadataKeys, \* the set of all possible metadata keys 
    MetadataValues, \* the non-finite set of all possible metadata values
    Exceptions \* The set of exceptions which may be raised.
    
    


ASSUME PathChars \in STRING
ASSUME Paths \in STRING

ASSUME Data \in STRING \* Really bytes, but it is irrelevant

(* There are some metadata keys which are system MD entries. These may be queried but not explictly set. *)

ASSUME MetadataKeys \in STRING

ASSUME MetadataValues \in STRING

ASSUME Timestamp \in Nat

----------------------------------------------------------------------------------------


(* 
There is a predicate to validate a pathname.
This is considered implementation-specific. It may be describable as a regular expression specific to each implementation,
though constraints such as "no two adjacent '/' characters" may make for a complex regexp. Perhaps a each FS would have a 
set of regexps which all must be valid for a path to be considered valid.*)

CONSTANT is_valid_pathname(_)
CONSTANT is_valid_metadata_key(_)

(* All paths can be evaluated to see if their pathname is valid *)

ASSUME \A p \in Paths: is_valid_pathname(p) \in BOOLEAN

(* All metadata keys can be evaluated for validity *)

ASSUME \A e \in MetadataKeys: is_valid_metadata_key(e) \in BOOLEAN

CONSTANT path_matches(_, _, _)

(* This should really be defined by looking inside the strings. It is: all paths starting with the prefix up to those ending in the suffix *)
ASSUME \A p in Paths, prefix in STRING, suffix in STRING: path_matches(p, prefix, suffix) \in BOOLEAN

----------------------------------------------------------------------------------------

VARIABLES
    store  \* The object store
    
----------------------------------------------------------------------------------------


----------------------------------------------------------------------------------------

(* Exception logic *)

Success == CHOOSE x: x \notin Exceptions


MetadataEntry == [
    key: MetadataKeys,     \* The key of the entry
    value: MetadataValues     \* the value of this metadata entry
    ]


Object == [
    path: Paths,     \* The path to the entry
    data: Data ,    \* the data in the entry
    metadata: MetadataEntry \* it's a set
    
    \* implicits: create time, modifieed
    ]

SystemMetadata == [
    size: Nat,
    timestamp: Nat
]

(*

A store : path -> (data, user-md, system-md)

update: PUT, DELETE
query: GET, HEAD, LIST(path) 
*) 

StoreTypeInvariant ==
    /\ store \in [Paths -> Data]
 
(* The initial state of the store is that it is empty *)
InitialState ==
    /\ StoreTypeInvariant
    /\ DOMAIN store = {}

PUT(path, data, result) ==
    /\ path \in Paths
    /\ data \in Data
    /\ store' = [store EXCEPT ![path] = data]
    /\ result = Success
 
GET(path, data, result) ==
    /\ path \in Paths 
    /\ path \in DOMAIN store
    /\ data = store[path]
    /\ UNCHANGED store
    /\ result = Success

HEAD(path, result) ==
    /\ path \in Paths 
    /\ path \in DOMAIN store
    /\ UNCHANGED store
    /\ result = Success

(* The DELETE operation will succeed even if the entry is not found. *)

DELETE(path, result) ==
    /\ path \in Paths 
    /\ store' = [p \in (DOMAIN store \ path) |-> store[p]]
    /\ result = Success

COPY(source, dest, result) ==
    /\ source \in DOMAIN store
    /\ dest \in Paths 
    /\ dest \notin DOMAIN store 
    /\ store' = [store EXCEPT ![dest] = store[source]]
    /\ result = Success
    
LIST(prefix, suffix, result) ==
    /\ prefix \in STRING
    /\ suffix \in STRING
    /\ result = \A p \in DOMAIN store : path_matches(p, prefix, suffix)
    /\ UNCHANGED store

-----

THEOREM InitialState => []StoreTypeInvariant



(*

Invariants

PUT is atomic

Eventually updates to the store are reflected in the index.

There may be a delay from a PUT/UPDATE/DELETE occuring and it being visible. 

How to model? One or more cached views?




Eventually, the state of the index matches that of the data in the store. That is: it will eventually become consistent.
A way to model this would be "updates to the index are serialized such that the index is updated in the same order which changes to the store take place".


1. All operations on an endpoint complete.
2. the exact order of arrival/queue may vary. That is: things may return before the side effects have taken place.
3. List -> directory
4.

*)

=============================================================================
\* Modification History
\* Last modified Wed Jul 20 22:37:57 BST 2016 by stevel
\* Created Sun Jun 19 18:07:44 BST 2016 by stevel


