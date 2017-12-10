


---------------------------- MODULE objectstore ----------------------------


EXTENDS FiniteSets, Sequences, Naturals, TLC


(*
============================================================================
Model of a Consistent S3 Object Store.
Author: Steve Loughran
============================================================================
*)

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




----------------------------------------------------------------------------------------

(*
============================================================================


A Path is a list of Path elements which represents a path to a file, directory or symbolic link

Path elements are non-empty strings. The exact set of valid strings MAY
be specific to a particular FileSystem implementation.

Path elements MUST NOT be in `{"", ".",  "..", "/"}`.

Path elements MUST NOT contain the characters `{'/', ':'}`.

Filesystems MAY have other strings that are not permitted in a path element.

When validating path elements, the exception `InvalidPathException` SHOULD
be raised when a path is invalid [HDFS]


============================================================================

*)

CONSTANTS
  Paths,          \* the non-finite set of all possible valid paths
  PathsAndRoot,   \* Paths and the "root" path; the latter is read-only
  Data,           \* the non-finite set of all possible sequences of bytes
  Timestamp,      \* A timestamp
  Byte,
  NonEmptyString


ASSUME NonEmptyString \in (STRING \ "")

ASSUME PathsAndRoot \in STRING
ASSUME Paths \in (PathsAndRoot \ "")


\* Timestamps are positive integers since the epoch.
ASSUME Timestamp \in Nat /\ Timestamp > 0

\* Byte type
ASSUME Byte \in 0..255

(* Data is a sequence of bytes *)
ASSUME Data \in Seq(Byte)


(*
 There is a predicate to validate a pathname.
 This is considered implementation-specific.

 It could be describable as a regular expression specific to each implementation,
 though constraints such as "no two adjacent '/' characters" might make for a complex regexp.
 Perhaps each FS would have a  set of regexps which all must be valid for
 a path to be considered valid.
 *)

CONSTANT is_valid_pathname(_)



(* All paths can be evaluated to see if their pathname is valid *)

ASSUME \A p \in Paths: is_valid_pathname(p) \in BOOLEAN


----------------------------------------------------------------------------------------



(*

============================================================================

This specification defines

* A model of a consistent object store: a consistent store of data and metadata,
  one without any notion of a "directory hierarchy". It is intended to model
  object stores such as Amazon S3, and includes its multipart PUT API.

* An API for communicating with object stores from Hadoop filesystems.

It is intended to be a foundation for defining algorithms with worth
with S3, such as the s3guard commit algorithm.

============================================================================

*)

CONSTANTS
  MetadataKeys,   \* the set of all possible metadata keys
  MetadataValues, \* the non-finite set of all possible metadata values
  Etag,
  MultipartPutId,
  PartId

(* There are some metadata keys which are system metadata entries.
   Those MAY be queried but SHALL NOT be explictly set. (more specifically, they'll be ignored if you try. *)

ASSUME MetadataKeys \in NonEmptyString

ASSUME MetadataValues \in STRING

ASSUME Etag \in NonEmptyString

ASSUME MultipartPutId \in NonEmptyString

(* Only 11,000 parts are allowed *)
ASSUME PartId \in 1..11000

----------------------------------------------------------------------------------------

CONSTANT is_valid_metadata_key(_)

(* All metadata keys can be evaluated for validity *)

ASSUME \A e \in MetadataKeys: is_valid_metadata_key(e) \in BOOLEAN

(* The patch matching algorithm used in the list operation *)

CONSTANT path_matches(_, _, _)


(* This should really be defined by looking inside the strings.
It is: all paths starting with the prefix up to those ending in the suffix *)

ASSUME \A p \in Paths, prefix, delimiter \in Paths: path_matches(p, prefix, delimiter) \in BOOLEAN


(* A function to return an etag of some data *)
CONSTANT etag_of(_)

(* A function to return an etag of a multipart operation; implementation specific*)
CONSTANT etag_of_multipart_operation(_)

(* Etags are strings, hence in MetadataValues. *)
ASSUME \A d \in Data: etag_of(d) \in Etag

(*
This is commented out as it is not a requirement that etags are the same for an equivalent sequence
of bytes. All that matters is that one is generated.
ASSUME \A d, e \in Data: d = e => etag_of(d) = etag_of(e) \in STRING
*)

----------------------------------------------------------------------------------------

VARIABLE store  \* The object store
VARIABLE pending \* Pending requests

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
  created: Timestamp,     \* timestamp
  etag: MetadataValues
  ]

ListingEntry == [
    path: Paths,            \* The path to the entry
    data: Data ,            \* the data in the entry
    created: Timestamp,     \* timestamp
    etag: MetadataValues,
    metadata: MetadataEntry \* it's a set
  ]

(* The check for a path having an entry is pulled out for declaring invariants *)
has_entry(s, p) == p \in DOMAIN s


PendingMultipartPartRequest == [
  putId: MultipartPutId,
  part: PartId,
  data: Data
]

PendingMultipartPartResponse == [
  etag: Etag
]

PendingMultipartPutPart == [
  data: Data,
  etag: Etag
]


(* A pending Multipart Upload has an ID and start timne, which is used to define the final
  create time of the committed operation *)
PendingMultipartOperation == [
\*  id: STRING,
  path: Paths,
  started: Timestamp,
  parts: [PartId -> PendingMultipartPutPart]
]



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
       /\ UNCHANGED <<store, pending>>
    \/ /\ validArgs
       /\ result' = Success
       /\ UNCHANGED pending
       /\ store' = [store EXCEPT ![path] = [data |-> data, created |-> current_time, etag |-> etag_of(data)]]


(*
GET: path -> data as well as summary metadata
*)
doGet(path, metadata, data, current_time, result) ==
  LET
    validArgs == path \in PathsAndRoot
    exists == has_entry(store, path)
    entry == store[path]
  IN
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED <<store, pending>>

    \/  /\ validArgs
        /\ path = ""
        /\ result' = Success
        /\ UNCHANGED <<store, pending>>
        /\ data' = {}

    \/  /\ validArgs
        /\ ~exists
        /\ result' = NotFound
        /\ UNCHANGED <<store, pending>>

    \/  /\ validArgs
        /\ exists
        /\ result' = Success
        /\ data' = store[path].data
        /\ metadata' = [created |-> entry.created, length |-> Len(entry.data), etag |-> entry.etag]
        /\ UNCHANGED <<store, pending>>

(*
HEAD: the metadata without the data
*)

doHead(path, metadata, current_time, result) ==
  LET
    validArgs == path \in PathsAndRoot
    exists == has_entry(store, path)
    entry == store[path]
  IN
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED <<store, pending>>
        
    \/  /\ validArgs
        /\ path = ""
        /\ result' = Success
        /\ metadata' = [created |-> 0, length |-> 0]
        /\ UNCHANGED <<store, pending>>

    \/  /\ validArgs
        /\ ~exists
        /\ result' = NotFound
        /\ UNCHANGED <<store, pending>>
        
    \/  /\ validArgs
        /\ exists
        /\ result' = Success
        /\ metadata' = [created |-> entry.created, length |-> Len(entry.data), etag |-> entry.etag]
        /\ UNCHANGED <<store, pending>>


doDelete(path, current_time, result) ==
  LET
    validArgs == path \in Paths
    exists == has_entry(store, path)
  IN
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED <<store, pending>>
        
    \/  /\ validArgs
        /\ ~exists
        /\ result' = NotFound
        /\ UNCHANGED <<store, pending>>
        
    \/  /\ validArgs
        /\ exists
        /\ result' = Success
        /\ store' = [p \in (DOMAIN store \ path) |-> store[p]]
        /\ UNCHANGED pending


doCopy(source, dest, current_time, result) ==
  LET
    validArgs == source \in Paths /\ dest \in Paths /\ current_time \in Timestamp
    exists == has_entry(store, source)
  IN
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED <<store, pending>>
        
    \/  /\ validArgs
        /\ ~exists
        /\ result' = NotFound
        /\ UNCHANGED <<store, pending>>
        
    \/  /\ validArgs
        /\ exists
        /\ result' = Success
        /\ store' = [store EXCEPT ![dest] = [data |-> store[source].data, created |-> current_time]]
        /\ UNCHANGED pending

(* The list operation returns the metadata of all entries in the object store whose path matches the prefix/suffix pattern.
S3 also returns a string sequence of common subpath underneath, essential "what look like directories" *)

pathsMatchingPrefix(prefix, suffix) == \A path \in DOMAIN store : path_matches(path, prefix, suffix)

doList(prefix, suffix, current_time, result, listing) ==
  LET
    validArgs == prefix \in STRING /\ suffix \in STRING
  IN
    \/  /\ ~validArgs
        /\ result' = BadRequest
        /\ UNCHANGED <<store, pending>>
        
    \/  /\ validArgs
        /\ result' = Success
        /\ listing' = [path \in pathsMatchingPrefix(prefix, suffix) |->
            [path |-> path,
             created |-> store[path].created,
             length |-> Len(store[path].data),
             etag |-> store[path].etag]]
        /\ UNCHANGED <<store, pending>>


(*
Initiate a multipart PUT. The destination is specified; the create time of the final artifact is set to the current server time.
A unique ID is returned.
There is no requirement for the destination to be unique: multiple requests may target the same destination, with the order of the commit
operation defining the order in which the results become visible.
*)


doInitiateMultipartPut(dest, current_time, result, operationId) ==
  LET
    validArgs == dest \in Paths /\ current_time \in Timestamp
    newPartId == CHOOSE id \in MultipartPutId: ~id \in DOMAIN pending
  IN
    \/ /\ ~validArgs
       /\ result' = BadRequest
       /\ UNCHANGED <<store, pending>>
       
    \/ /\ validArgs
       /\ result' = Success
       /\ UNCHANGED store
       /\ operationId' = newPartId 
       /\ pending' = [pending EXCEPT ![newPartId] =
           [path |-> dest, created |-> current_time]]

(*
PUT a single part for an operation.
Result is an etag to be used for the ordered sequence

*)
doPutPart(operationId, partId, part_data, current_time, result, etagResult) ==
  LET
    validArgs == operationId \in DOMAIN pending /\ part_data \in Data /\ partId \in PartId
    etagVal == etag_of(part_data)
  IN
    \/ /\ ~validArgs
       /\ result' = BadRequest
       /\ UNCHANGED <<store, pending>>
       
    \/ /\ validArgs
       /\ result' = etagVal
       /\ etagResult' = etagVal
       /\ UNCHANGED store
       /\ pending' = [pending EXCEPT
           ![operationId] = [
            path |-> pending[operationId].dest,
            parts  |-> [pending[operationId].parts EXCEPT
             ![partId] =  [data |-> part_data, etag |-> etagVal] ]
            ]
         ]

(*
  The commit operation is the most complex. The part list supplied defines the order in which the supplied parts
  are saved to the store.
	TODO: work out how to declare that all data is the ordered appending of the data of the list of parts. Recurse?

   \* alldata == \A [part \in (1...Len(parts) -1]) Append(upload[parts[part]], upload[parts[part + 1])

*)
doCommitMultipartPut(operationId, parts, current_time, result) ==
 LET 
   upload == pending[operationId]
   validArgs == (operationId \in DOMAIN pending) /\ (parts \in Seq(PartId)) 
     /\ (\A p \in parts: p \in DOMAIN upload.parts) /\ (\A p \in DOMAIN upload.parts: p \in parts)  
	 alldata == parts
	 etag == etag_of_multipart_operation(upload)
 IN
   \/ /\ ~validArgs
      /\ result' = BadRequest
      /\ UNCHANGED <<store, pending>>
      
   \/ /\ validArgs
      /\ result' = Success
      /\ pending' = [p \in (DOMAIN pending \ operationId) |-> pending[p]]
      /\ store' = [store EXCEPT ![upload.path] = [data |-> alldata, created |-> upload.created, etag |-> etag]]


(*
  Abort the multipart put operation.
  All pending data is deleted; the pending operation record removed. 
 *)
doAbortMultipartPut(operationId, current_time, result) ==
LET 
  validArgs == operationId \in DOMAIN pending 
IN
  \/ /\ ~validArgs
     /\ result' = BadRequest
     /\ UNCHANGED <<store, pending>>
     
  \/ /\ validArgs
     /\ result' = Success
     /\ UNCHANGED store
     /\ pending' = [p \in (DOMAIN pending \ operationId) |-> pending[p]]
  

---------


\* PutInvariant  == \A p in Paths: doDelete(p, Success) => ~has_entry(store', p)


\* DeleteInvariant == \A p in Paths: doDelete(p, Success) => ~has_entry(store', p)




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


process(request, result, metadata, body, current_time) ==
  LET verb == request.verb
  IN
    \/ verb = "PUT"    /\ doPut(request.path, request.data, current_time, result)
    \/ verb = "GET"    /\ doGet(request.path, metadata, body, current_time, result)
    \/ verb = "HEAD"   /\ doHead(request.path, metadata, current_time, result)
    \/ verb = "DELETE" /\ doDelete(request.path, current_time, result)
    \/ verb = "COPY"   /\ doCopy(request.source, request.dest, current_time, result)
    \/ verb = "LIST"   /\ doList(request.prefix, request.suffix, current_time, result, body)




(*
The store state invariant not only declares the type of the store, it declares
attributes of the has_entry operator which are superfluous given the definition
of has_entry() as the path being in the domain of the store. It's explicit
for those implementors planning to write tests.
*)

StoreStateInvariant ==
  /\ store \in [Paths -> StoreEntry]
  /\ pending \in [MultipartPutId -> PendingMultipartOperation]


(* The initial state of the store is that it is empty. *)
(* Notice how this ignores the root entry, "".
 This is a special entry: object stores are not filesystems: there is no root node equivalent to "/" *)
InitialStoreState ==
  /\ StoreStateInvariant
  /\ DOMAIN store = {}
  /\ DOMAIN pending = {}

(*
The amount of data you get back is the amount of data you are told comes back.
*)
(*
GetLengthInvariant ==
  \A path \in Paths, sysMd \in SystemMetadata, data \in Data, t \in Timestamp :
    doGet(path, sysMd, data, t, Success) ==> Len(data) == sysMd.length
*)

THEOREM   \A path \in Paths, sysMd \in SystemMetadata, data \in Data, t \in Timestamp :
    TRUE




(*
*)

(* The metadata that comes from a doHead() MUST match that from a doGet() *)
(* See: HADOOP-11202 SequenceFile crashes with encrypted files that are shorter than FileSystem.getStatus(path) *)
(*
THEOREM GetAndHeadInvariant =>
  \A path \in Path, sysMd \in SystemMetadata, data \in Data, t \in Timestamp :
    doGet(path, sysMd, data, t, Success) ==> doHead(path, sysMd, t, Success)
*)
(* The details you get back in a listing match the details you get back from a doGet call on the specific path *)
(* of course, on an eventually consistent object store, there may be lag *)

(*

  TODO: ListAndGetInvariant
  The subset of metadata returned from a listing matches that of the individual records
  returned in HEAD and GET.  
  
  

*)


-----

THEOREM InitialStoreState => []StoreStateInvariant






=============================================================================
\* Modification History
\* Last modified Sun Dec 10 21:53:18 GMT 2017 by stevel
\* Created Sun Jun 19 18:07:44 BST 2016 by stevel


