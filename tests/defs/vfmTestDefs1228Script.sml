open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1228";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverH_prefixed0.json";
val defs = mapi (define_test "1228") tests;
val () = export_theory_no_docs ();
