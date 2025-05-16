open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2178";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callToCallCodeOpCodeCheck.json";
val defs = mapi (define_test "2178") tests;
val () = export_theory_no_docs ();
