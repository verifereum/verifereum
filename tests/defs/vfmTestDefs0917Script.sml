open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0917";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/rangesExample.json";
val defs = mapi (define_test "0917") tests;
val () = export_theory_no_docs ();
