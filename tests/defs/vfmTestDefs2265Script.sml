open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2265";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_InternalCallStoreClearsOOG.json";
val defs = mapi (define_test "2265") tests;
val () = export_theory_no_docs ();
