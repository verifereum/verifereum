open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2103";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallGoesOOGOnSecondLevel2.json";
val defs = mapi (define_test "2103") tests;
val () = export_theory_no_docs ();
