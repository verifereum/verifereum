open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1311";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEIdentity_4_gas17.json";
val defs = mapi (define_test "1311") tests;
val () = export_theory_no_docs ();
