open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1190";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEIdentity_2.json";
val defs = mapi (define_test "1190") tests;
val () = export_theory_no_docs ();
