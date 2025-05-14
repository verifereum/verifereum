open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2374";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecall_10.json";
val defs = mapi (define_test "2374") tests;
val () = export_theory_no_docs ();
