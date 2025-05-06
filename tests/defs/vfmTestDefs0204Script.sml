open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0204";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7685_general_purpose_el_requests/multi_type_requests/invalid_multi_type_requests.json";
val defs = mapi (define_test "0204") tests;
val () = export_theory_no_docs ();
