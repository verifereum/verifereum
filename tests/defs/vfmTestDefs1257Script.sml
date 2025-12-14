open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1257";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEEcrecover2.json";
val defs = mapi (define_test "1257") tests;
val () = export_theory_no_docs ();
