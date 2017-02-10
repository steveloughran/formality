


---------------------------- MODULE objectstore ----------------------------


EXTENDS FiniteSets, Sequences, Naturals, TLC

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

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL
      NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED",  "MAY", and
      "OPTIONAL" in this document are to be interpreted as described in
      RFC 2119.

 *)


(*

============================================================================

This specification defines

1. A model of an object store: a  consistent store of data and metadata,
   one without any notion of a "directory hierarchy". It is intended to model
   object stores such as Amazon S3 and OpenStack swift, while leaving scope for
   optional features which may only be available on other stores.

2. An API for communicating with object stores from Hadoop filesystems. 

3. How the Object Store API must translate into changes in the state of the Object Store
   itself. That is: what MUST an implementation do?


============================================================================

*)

CONSTANTS
  Paths,         \* the non-finite set of all possible valid paths
  Data,          \* the non-finite set of all possible sequences of bytes
  MetadataKeys, \* the set of all possible metadata keys 
  MetadataValues, \* the non-finite set of all possible metadata values
  Timestamp, \* A timestamp
  Byte


ASSUME Paths \in (STRING \ "")


(* There are some metadata keys which are system MD entries. Those MAY be queried but SHALL NOT be explictly set. *)

ASSUME MetadataKeys \in (STRING \ "")

ASSUME MetadataValues \in (STRING \ "")

\* Timestamps are positive integers since the epoch.
ASSUME Timestamp \in Nat /\ Timestamp > 0

ASSUME Byte \in 0..256


ASSUME Data \in Seq(Byte) 

----------------------------------------------------------------------------------------


(* 
 There is a predicate to validate a pathname.
 This is considered implementation-specific.

 It could be describable as a regular expression specific to each implementation,
 though constraints such as "no two adjacent '/' characters" might make for a complex regexp. 
 Perhaps each FS would have a  set of regexps which all must be valid for
 a path to be considered valid.
 *)

CONSTANT is_valid_pathname(_)
CONSTANT is_valid_metadata_key(_)

(* All paths can be evaluated to see if their pathname is valid *)

ASSUME \A p \in Paths: is_valid_pathname(p) \in BOOLEAN

(* All metadata keys can be evaluated for validity *)

ASSUME \A e \in MetadataKeys: is_valid_metadata_key(e) \in BOOLEAN

(* The patch matching algorithm used in the list operation *)

CONSTANT path_matches(_, _, _)

(* This should really be defined by looking inside the strings. 
It is: all paths starting with the prefix up to those ending in the suffix *)

ASSUME \A p \in Paths, prefix, delimiter \in Paths: path_matches(p, prefix, delimiter) \in BOOLEAN


----------------------------------------------------------------------------------------

VARIABLES
    store  \* The object store
    
----------------------------------------------------------------------------------------



----------------------------------------------------------------------------------------

(* Exception logic *)

BadRequest == "BadRequest"
NotFound == "NotFound"
Success == "Success"


MetadataEntry == [
    key: MetadataKeys,     \* The key of the entry
    value: MetadataValues     \* the value of this metadata entry
    ]


SystemMetadata == [
  size: Nat,
  created: Timestamp
  ]

(*

A store : path -> (data, user-md, system-md)

update: PUT, DELETE
query: GET, HEAD, LIST(path) 
*) 


StoreEntry == [
    data: Data ,            \* the data in the entry
    created: Timestamp     \* timestamp    
  ]

ListingEntry == [
    path: Paths,            \* The path to the entry
    data: Data ,            \* the data in the entry
    created: Timestamp,     \* timestamp    
    metadata: MetadataEntry \* it's a set
  ]
  
(* The check for a path having an entry is pulled out for declaring invariants *)
has_entry(s, p) == p \in DOMAIN s




(*
The store state invariant not only declares the type of the store, it declares
attributes of the has_entry operator which are superfluous given the definition
of has_entry() as the path being in the domain of the store. It's explicit
for those implementors planning to write tests.
*)

StoreStateInvariant ==
  /\ store \in [Paths -> StoreEntry]
  /\ \A path \in DOMAIN store: has_entry(store, path)
  /\ \A path \in (Paths \ DOMAIN store): ~has_entry(store, path)
  
 
(* The initial state of the store is that it is empty. *)
(* Notice how this ignores the root entry, "".
 This is a special entry: object stores are not filesystems: there is no root node equivalent to "/" *)
InitialStoreState ==
  /\ StoreStateInvariant
  /\ DOMAIN store = {}


---- 

(*
Actions.
Note how some post conditions are explicitly called out. They are superfluous, in the model, but they do declare
final state for testability
*)

(*
 PUT: update the store with the newly uploaded data.
 This definition is consistent: the store changes are immediately visible, even if there was an existing
 entry.
*)

doPut(path, data, current_time, result) ==
  LET validArgs == path \in Paths /\ data \in Data /\ current_time \in Timestamp
  IN 
    \/ /\ ~validArgs
       /\ result' = BadRequest
       /\ UNCHANGED store
    \/ /\ validArgs
       /\ result' = Success
       /\ store' = [store EXCEPT ![path] = [data |-> data, created |-> current_time]]


(*
GET: path -> data as well as summary metadata
*) 
doGet(path, result, metadata, data) ==
  LET
    validArgs == path \in Paths /\ data \in Data
    exists == has_entry(store, path)
  IN     
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED store
    \/  /\ validArgs
        /\ ~exists
        /\ result' = NotFound
        /\ UNCHANGED store
    \/  /\ validArgs
        /\ exists
        /\ result' = Success
        /\ data' = store[path].data
        /\ metadata' = [created |-> store[path].created, length |-> Len(store[path].data)]
        /\ UNCHANGED store

(*
HEAD: the metadata without the data
*)

(*
doHead2(path, result, metadata) ==
 LET
   data == d \in Data
 IN
  doGet(path, result', data, metadata') 
*)

(*
HEAD: the metadata without the data
*)

doHead(path, result, metadata) ==
  LET
    validArgs == path \in Paths
    exists == has_entry(store, path)
  IN     
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED store
    \/  /\ validArgs
        /\ ~exists
        /\ result' = NotFound
        /\ UNCHANGED store
    \/  /\ validArgs
        /\ exists
        /\ result' = Success
        /\ metadata' = [created |-> store[path].created, length |-> Len(store[path].data)]
        /\ UNCHANGED store


doDelete(path, result) ==
  LET
    validArgs == path \in Paths
    exists == has_entry(store, path)
  IN     
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED store
    \/  /\ validArgs
        /\ ~exists
        /\ result' = NotFound
        /\ UNCHANGED store
    \/  /\ validArgs
        /\ exists
        /\ result' = Success
        /\ store' = [p \in (DOMAIN store \ path) |-> store[p]]


doCopy(source, dest, current_time, result) ==
  LET
      validArgs == source \in Paths /\ dest \in Paths /\ current_time \in Timestamp
      exists == has_entry(store, source)
  IN     
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED store
    \/  /\ validArgs
        /\ ~exists
        /\ result' = NotFound
        /\ UNCHANGED store
    \/  /\ validArgs
        /\ exists
        /\ result' = Success
        /\ store' = [store EXCEPT ![dest] = [data |-> store[source].data, created |-> current_time]]

(* The list operation returns the metadata of all entries in the object store whose path matches the prefix/suffix pattern.
S3 also returns a string sequence of common subpath underneath, essential "what look like directories" *)

pathsMatchingPrefix(prefix, suffix) == \A path \in DOMAIN store : path_matches(path, prefix, suffix)

doList(prefix, suffix, result, listing) ==
    /\ prefix \in STRING
    /\ suffix \in STRING
    /\ result' = Success
    /\ listing' = [path \in pathsMatchingPrefix(prefix, suffix) |->
        [path |-> path, created |-> store[path].created, length |-> Len(store[path].data)]]
    /\ UNCHANGED store


---------


\* PutInvariant  == \A p in Paths: doDelete(p, Success) => ~has_entry(store', p)
       

\* DeleteInvariant == \A p in Paths: doDelete(p, Success) => ~has_entry(store', p)

(* The amount of data you get back is the amount of data you are told comes back. *)

(*
GetLengthInvariant ==
  \A path \in DOMAIN store, sysMd \in SystemMetadata, data \in Data :
    doGet(path, Success, data, sysMd) ==> Len(data) = sysMd.length
*)

(* The metadata that comes from a doHead() MUST match that from a doGet() *)
(* See: HADOOP-11202 SequenceFile crashes with encrypted files that are shorter than FileSystem.getStatus(path) *)
(*
GetAndHeadInvariant ==
  \A path \in DOMAIN store, sysMd \in SystemMetadata, data \in Data :
    doGet(path, Success, data, sysMd) ==> doHead(path, Success, sysMd) 
*)

(* The details you get back in a listing match the details you get back from a doGet call on the specific path *)
(* of course, on an eventually consistent object store, there may be lag *)

(*
  
  ListAndGetInvariant == TODO 
    
*)



(* now define action messages which can be queued for processing; we consider them to processed in a serial order *)

----------------------------------------------------------------------------------------

(* Action Records *)

putAction == [
  verb: "PUT",
  path: STRING,
  data: [Nat -> Nat]
]

deleteAction == [
  verb: "DELETE",
  path: STRING
]

getAction == [
  verb: "GET",
  path: STRING,
  data: STRING
]

headAction == [
  verb: "HEAD",
  path: STRING
]

copyAction == [
  verb: "COPY",
  source: STRING,
  dest: STRING
]

listAction == [
  verb: "LIST",
  prefix: STRING,
  delimiter: STRING
]

(* Process a request, generate a result. *)
(* TODO: merge GET data into result *)
(*
process(request, result, current_time) == 
  LET verb == request.verb
  IN
    \/ verb = "PUT"    /\ doPut(request.path, request.data, current_time, result)
    \/ verb = "GET"    /\ doGet(request.path, request.data, result)
    \/ verb = "HEAD"   /\ doHead(request.path, result)
    \/ verb = "DELETE" /\ doDelete(request.path, result)
    \/ verb = "COPY"   /\ doCopy(request.source, request.dest, current_time, result)
    \/ verb = "LIST"   /\ doList(request.prefix, request.suffix, result)
    
*)


-----

THEOREM InitialStoreState => []StoreStateInvariant




=============================================================================
\* Modification History
\* Last modified Thu Oct 06 15:30:47 BST 2016 by stevel
\* Created Sun Jun 19 18:07:44 BST 2016 by stevel


