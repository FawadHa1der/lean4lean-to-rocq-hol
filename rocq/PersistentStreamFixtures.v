(* Test-only literal nested inputs. No generated expected answer is installed. *)
From Stdlib Require Import List NArith.
From LeanPort Require Import Syntax Checker PersistentIndex PersistentAdmission
  NestedRegression StringParityFixtures.
Import ListNotations.
Module NR := NestedRegression.NestedRegression.

Definition nested_box_batch := BatchInductive [NR.box_decl] [NR.box_ctor] [NR.box_rec].
Definition nested_tree_batch := BatchInductive [NR.tree_decl 1]
  [NR.leaf_ctor;NR.node_ctor] [NR.tree_rec;NR.tree_aux_rec].
Definition nested_mutations :=
  [BatchInductive [NR.tree_decl 0] [NR.leaf_ctor;NR.node_ctor] [NR.tree_rec;NR.tree_aux_rec];
   BatchInductive [NR.tree_decl 1] [NR.leaf_ctor;NR.node_ctor] [NR.tree_rec];
   BatchInductive [NR.tree_decl 1] [NR.leaf_ctor;NR.node_ctor]
     [NR.with_rec_k NR.tree_rec true;NR.tree_aux_rec];
   BatchInductive [NR.tree_decl 1]
     [NR.leaf_ctor;NR.ctor_decl NR.node NR.tree 1 0 0 (decl_type NR.node_ctor)]
     [NR.tree_rec;NR.tree_aux_rec];
   BatchInductive [NR.tree_decl 1] [NR.leaf_ctor;NR.node_ctor]
     [NR.tree_rec;NR.with_rules NR.tree_aux_rec []]].
Definition persistent_nested_baseline :=
  state_stream 256 (seed_state (fun _ => 0%N) []) [nested_box_batch;nested_tree_batch].

Example persistent_nested_positive :
  match persistent_nested_baseline with Accept _ => true | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Example persistent_nested_complete_result :
  project_result persistent_nested_baseline = NR.tree_admission.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions persistent_nested_positive.
Print Assumptions persistent_nested_complete_result.
