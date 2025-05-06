open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2288";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callOutput3.json";
val defs = mapi (define_test "2288") tests;
val () = export_theory_no_docs ();
