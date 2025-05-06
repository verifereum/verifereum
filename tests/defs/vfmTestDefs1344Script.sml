open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1344";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverR_prefixed0.json";
val defs = mapi (define_test "1344") tests;
val () = export_theory_no_docs ();
