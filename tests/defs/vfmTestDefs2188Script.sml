open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2188";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call50000_identity2.json";
val defs = mapi (define_test "2188") tests;
val () = export_theory_no_docs ();
