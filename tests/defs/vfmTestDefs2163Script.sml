open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2163";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_RevertDepth2.json";
val defs = mapi (define_test "2163") tests;
val () = export_theory_no_docs ();
