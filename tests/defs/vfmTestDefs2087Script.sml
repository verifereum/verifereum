open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2087";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecover0_Gas2999.json";
val defs = mapi (define_test "2087") tests;
val () = export_theory_no_docs ();
