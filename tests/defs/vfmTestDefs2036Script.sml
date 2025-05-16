open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2036";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/tx_e1c174e2.json";
val defs = mapi (define_test "2036") tests;
val () = export_theory_no_docs ();
