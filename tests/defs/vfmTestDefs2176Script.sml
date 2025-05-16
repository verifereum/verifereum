open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2176";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callOutput3partial.json";
val defs = mapi (define_test "2176") tests;
val () = export_theory_no_docs ();
