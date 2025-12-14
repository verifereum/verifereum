open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1277";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODESha256_2.json";
val defs = mapi (define_test "1277") tests;
val () = export_theory_no_docs ();
