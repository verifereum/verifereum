open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1255";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEEcrecover0_overlappingInputOutput.json";
val defs = mapi (define_test "1255") tests;
val () = export_theory_no_docs ();
