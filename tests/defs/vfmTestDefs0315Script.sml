open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0315";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/19_oogUndoesTransientStore.json";
val defs = mapi (define_test "0315") tests;
val () = export_theory_no_docs ();
