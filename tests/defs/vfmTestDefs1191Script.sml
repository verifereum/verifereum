open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1191";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEIdentity_3.json";
val defs = mapi (define_test "1191") tests;
val () = export_theory_no_docs ();
