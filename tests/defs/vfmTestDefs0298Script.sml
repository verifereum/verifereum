open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0298";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7685_general_purpose_el_requests/test_valid_multi_type_requests.json";
val defs = mapi (define_test "0298") tests;
val () = export_theory_no_docs ();
