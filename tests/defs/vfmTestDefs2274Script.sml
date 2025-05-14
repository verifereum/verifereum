open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2274";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_PostToReturn1.json";
val defs = mapi (define_test "2274") tests;
val () = export_theory_no_docs ();
