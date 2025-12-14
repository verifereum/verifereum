open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0335";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_measurements.json";
val defs = mapi (define_test "0335") tests;
val () = export_theory_no_docs ();
