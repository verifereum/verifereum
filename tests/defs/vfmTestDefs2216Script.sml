open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2216";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallGoesOOGOnSecondLevel.json";
val defs = mapi (define_test "2216") tests;
val () = export_theory_no_docs ();
