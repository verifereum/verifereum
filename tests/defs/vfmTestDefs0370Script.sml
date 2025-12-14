open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0370";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_tstore_available_at_correct_address.json";
val defs = mapi (define_test "0370") tests;
val () = export_theory_no_docs ();
