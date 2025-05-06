open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0806";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeSizeLimit/codesizeValid.json";
val defs = mapi (define_test "0806") tests;
val () = export_theory_no_docs ();
