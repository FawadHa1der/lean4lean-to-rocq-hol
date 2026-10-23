(* Test-only checked inputs; no fixture declaration bypasses admission. *)
From Stdlib Require Import List NArith.
From LeanPort Require Import Syntax Checker Declarations Inductive MetadataFixtures
  PersistentAdmission PersistentIndex AdmissionDelta.
Import ListNotations.

Definition generated_batch env ps np specs : result admission_batch :=
  generated <- derive_inductive Metadata.fuel env ps np specs ;;
  Accept (BatchInductive (filter Metadata.is_ind generated)
    (filter Metadata.is_ctor generated) (filter Metadata.is_rec generated)).

Definition test_prop := ESort LZero.
Definition test_name i := NameNum NameAnon i.
Definition test_p := test_name 1.
Definition test_h := test_name 2.
Definition test_p_expr := EConst test_p [].
Definition test_h_expr := EConst test_h [].
Definition simple_stream :=
  [BatchOrdinary (InputAxiom test_p [] test_prop false);
   BatchOrdinary (InputAxiom test_h [] test_p_expr false)].

Example empty_stream_accepts :
  project_result (state_stream 0 (seed_state (fun _ => 0%N) []) []) = Accept [].
Proof. reflexivity. Qed.
Example simple_stream_positive :
  match state_stream 16 (seed_state (fun _ => 0%N) []) simple_stream with
  | Accept _ => true | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Example unsupported_stream_declines :
  project_result (state_stream 16 (seed_state (fun _ => 0%N) [])
    [BatchOrdinary InputUnsupported]) = Decline UnsupportedDeclaration.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_stream_rejects :
  project_result (state_stream 16 (seed_state (fun _ => 0%N) [])
    (simple_stream ++ [BatchOrdinary (InputAxiom test_p [] test_prop false)])) =
    Reject DuplicateDeclaration.
Proof. vm_compute. reflexivity. Qed.
