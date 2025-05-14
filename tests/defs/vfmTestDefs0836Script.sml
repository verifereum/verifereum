open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0836";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/RevertDepthCreate2OOGBerlin.json";
val defs = mapi (define_test "0836") tests;
val () = export_theory_no_docs ();
