open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2217";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecoverR_prefixed0.json";
val defs = mapi (define_test "2217") tests;
val () = export_theory_no_docs ();
