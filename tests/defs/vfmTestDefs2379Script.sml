open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2379";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/callValue.json";
val defs = mapi (define_test "2379") tests;
val () = export_theory_no_docs ();
