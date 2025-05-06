open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0805";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeSizeLimit/codesizeOOGInvalidSize.json";
val defs = mapi (define_test "0805") tests;
val () = export_theory_no_docs ();
