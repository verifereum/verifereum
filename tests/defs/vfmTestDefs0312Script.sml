open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0312";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_delegation_clearing_and_set.json";
val defs = mapi (define_test "0312") tests;
val () = export_theory_no_docs ();
