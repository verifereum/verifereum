open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0923";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json";
val defs = mapi (define_test "0923") tests;
val () = export_theory_no_docs ();
