open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2256";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecall_10.json";
val defs = mapi (define_test "2256") tests;
val () = export_theory_no_docs ();
