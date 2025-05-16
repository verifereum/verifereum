open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0693";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeSizeLimit/codesizeValid.json";
val defs = mapi (define_test "0693") tests;
val () = export_theory_no_docs ();
