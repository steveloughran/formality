----------------------------- MODULE filesystem -----------------------------


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


CONSTANTS
  Paths,          \* the non-finite set of all possible valid paths
  PathsAndRoot,   \* Paths and the "root" path; the latter is read-only
  Data,           \* the non-finite set of all possible sequences of bytes
  Timestamp,      \* A timestamp
  Byte,
  NonEmptyString,
  IllegalPathString,
  IllegalPathChar,
  PathElement


ASSUME NonEmptyString \in (STRING \ "")

ASSUME PathsAndRoot \in STRING
ASSUME Paths \in (PathsAndRoot \ "")
ASSUME IllegalPathString \in {"", ".", ".." }
ASSUME IllegalPathChar \in {"/", ":"}

(* TODO: some declare that you can't have any of the illegal path chars in an path element *)
ASSUME PathElement \in (STRING \ IllegalPathString )

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

 
CONSTANT is_valid_pathelement(_)



(* All paths can be evaluated to see if their pathname is valid *)

ASSUME \A p \in Paths: is_valid_pathname(p) \in BOOLEAN

========================