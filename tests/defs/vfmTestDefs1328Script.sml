open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1328";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODESha256_3_postfix0.json";
val defs = mapi (define_test "1328") tests;
val () = export_theory_no_docs ();
