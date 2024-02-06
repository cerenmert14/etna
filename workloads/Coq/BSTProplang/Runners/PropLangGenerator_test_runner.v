From BSTProplang Require Import PropLangGenerator.
From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".
Axiom num_tests : nat. Extract Constant num_tests => "max_int".

Definition qctest_test_prop_InsertValid := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertValid_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteValid := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteValid_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionValid := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionValid_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertPost := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertPost_runner))) ++ "}|]")).
Definition qctest_test_prop_DeletePost := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeletePost_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionPost := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionPost_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertModel := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertModel_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteModel := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteModel_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionModel := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionModel_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertInsert := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertInsert_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertDelete := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertDelete_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertUnion := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertUnion_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteInsert := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteInsert_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteDelete := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteDelete_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteUnion := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteUnion_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionDeleteInsert := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionDeleteInsert_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionUnionIdem := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionUnionIdem_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionUnionAssoc := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionUnionAssoc_runner))) ++ "}|]")).


Parameter OCamlString : Type.
Extract Constant OCamlString => "string".
Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    (""test_prop_InsertValid"", qctest_test_prop_InsertValid); (""test_prop_DeleteValid"", qctest_test_prop_DeleteValid); (""test_prop_UnionValid"", qctest_test_prop_UnionValid); (""test_prop_InsertPost"", qctest_test_prop_InsertPost); (""test_prop_DeletePost"", qctest_test_prop_DeletePost); (""test_prop_UnionPost"", qctest_test_prop_UnionPost); (""test_prop_InsertModel"", qctest_test_prop_InsertModel); (""test_prop_DeleteModel"", qctest_test_prop_DeleteModel); (""test_prop_UnionModel"", qctest_test_prop_UnionModel); (""test_prop_InsertInsert"", qctest_test_prop_InsertInsert); (""test_prop_InsertDelete"", qctest_test_prop_InsertDelete); (""test_prop_InsertUnion"", qctest_test_prop_InsertUnion); (""test_prop_DeleteInsert"", qctest_test_prop_DeleteInsert); (""test_prop_DeleteDelete"", qctest_test_prop_DeleteDelete); (""test_prop_DeleteUnion"", qctest_test_prop_DeleteUnion); (""test_prop_UnionDeleteInsert"", qctest_test_prop_UnionDeleteInsert); (""test_prop_UnionUnionIdem"", qctest_test_prop_UnionUnionIdem); (""test_prop_UnionUnionAssoc"", qctest_test_prop_UnionUnionAssoc)
  ] in
  let test = List.assoc test_name test_map in
  test ()


let () =
  Sys.argv.(1) |> qctest_map
".

Extraction "PropLangGenerator_test_runner.ml" qctest_test_prop_InsertValid qctest_test_prop_DeleteValid qctest_test_prop_UnionValid qctest_test_prop_InsertPost qctest_test_prop_DeletePost qctest_test_prop_UnionPost qctest_test_prop_InsertModel qctest_test_prop_DeleteModel qctest_test_prop_UnionModel qctest_test_prop_InsertInsert qctest_test_prop_InsertDelete qctest_test_prop_InsertUnion qctest_test_prop_DeleteInsert qctest_test_prop_DeleteDelete qctest_test_prop_DeleteUnion qctest_test_prop_UnionDeleteInsert qctest_test_prop_UnionUnionIdem qctest_test_prop_UnionUnionAssoc qctest_map.