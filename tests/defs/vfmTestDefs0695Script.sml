open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0695";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeSizeLimit/createCodeSizeLimit.json";
val defs = mapi (define_test "0695") tests;
val () = export_theory_no_docs ();
