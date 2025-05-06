open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2280";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ZeroValue_SUICIDE_OOGRevert.json";
val defs = mapi (define_test "2280") tests;
val () = export_theory_no_docs ();
