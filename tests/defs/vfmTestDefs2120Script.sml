open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2120";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRecursiveBombPreCall.json";
val defs = mapi (define_test "2120") tests;
val () = export_theory_no_docs ();
