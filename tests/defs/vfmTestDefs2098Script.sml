open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2098";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecoverH_prefixed0.json";
val defs = mapi (define_test "2098") tests;
val () = export_theory_no_docs ();
