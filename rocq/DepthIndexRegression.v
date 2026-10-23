(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import List PArith.BinPos FSets.FMapPositive.
From LeanPort Require Import Syntax DagScope DagMemo CacheIndexRefinement.
Import ListNotations.
Module D := DagMemo.
Definition path_a : D.context_path := [(1%positive,None)].
Definition path_b : D.context_path := [(2%positive,None)].
Definition path_v1 : D.context_path := [(1%positive,Some 1%positive)].
Definition path_v2 : D.context_path := [(1%positive,Some 2%positive)].
Definition value_a : result expr := Accept (ESort LZero).
Definition value_b : result expr := Reject TypeMismatch.
Definition depth_cache := D.cache_add (1%positive,path_b) value_b
  (D.cache_add (1%positive,path_a) value_a (PositiveMap.empty _)).

Example same_depth_really_collides : D.path_bucket path_a = D.path_bucket path_b.
Proof. reflexivity. Qed.
Example same_depth_type_a_kept : D.cache_find (1%positive,path_a) depth_cache = Some value_a.
Proof. reflexivity. Qed.
Example same_depth_type_b_kept : D.cache_find (1%positive,path_b) depth_cache = Some value_b.
Proof. reflexivity. Qed.
Example no_value_is_not_some_value :
  D.cache_find (1%positive,path_v1) depth_cache = None.
Proof. reflexivity. Qed.
Example distinct_let_values_kept :
  let cache := D.cache_add (1%positive,path_v2) (Decline OutOfFuel)
    (D.cache_add (1%positive,path_v1) value_a (PositiveMap.empty _)) in
  D.cache_find (1%positive,path_v1) cache = Some value_a /\
  D.cache_find (1%positive,path_v2) cache = Some (Decline OutOfFuel).
Proof. split; reflexivity. Qed.
Example tail_difference_kept :
  let a := (1%positive,None)::path_a in
  let b := (1%positive,None)::path_b in
  let cache := D.cache_add (1%positive,b) value_b
    (D.cache_add (1%positive,a) value_a (PositiveMap.empty _)) in
  D.cache_find (1%positive,a) cache = Some value_a /\
  D.cache_find (1%positive,b) cache = Some value_b.
Proof. split; reflexivity. Qed.
Example unequal_depths_are_separate :
  D.path_bucket path_a <> D.path_bucket ((1%positive,None)::path_a).
Proof. discriminate. Qed.
Example same_prefix_at_other_depth_is_absent :
  D.cache_find (1%positive,(1%positive,None)::path_a) depth_cache = None.
Proof. reflexivity. Qed.
Example empty_path_is_distinct :
  D.cache_find (1%positive,[]) depth_cache = None.
Proof. reflexivity. Qed.
Example distinct_node_is_absent : D.cache_find (2%positive,path_a) depth_cache = None.
Proof. reflexivity. Qed.
Example same_query_newest_value_wins :
  D.cache_find (1%positive,path_a)
    (D.cache_add (1%positive,path_a) (Decline UnsupportedExpression) depth_cache) =
  Some (Decline UnsupportedExpression).
Proof. reflexivity. Qed.
Example unrelated_old_bucket_survives :
  D.cache_find (1%positive,path_b)
    (D.cache_add (1%positive,[]) (Reject UnknownConstant) depth_cache) = Some value_b.
Proof. reflexivity. Qed.

Print Assumptions cache_add_refines.
