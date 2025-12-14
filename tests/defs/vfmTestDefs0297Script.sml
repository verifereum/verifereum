open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0297";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7685_general_purpose_el_requests/test_valid_multi_type_request_from_same_tx.json";
val defs = mapi (define_test "0297") tests;
val () = export_theory_no_docs ();
