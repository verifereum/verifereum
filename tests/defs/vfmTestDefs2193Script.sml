open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2193";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call50000_rip160.json";
val defs = mapi (define_test "2193") tests;
val () = export_theory_no_docs ();
