open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1318";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODERipemd160_5.json";
val defs = mapi (define_test "1318") tests;
val () = export_theory_no_docs ();
