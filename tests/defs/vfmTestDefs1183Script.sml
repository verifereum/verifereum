open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1183";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEEcrecoverR_prefixed0.json";
val defs = mapi (define_test "1183") tests;
val () = export_theory_no_docs ();
