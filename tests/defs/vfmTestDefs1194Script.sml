open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1194";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEIdentity_4_gas18.json";
val defs = mapi (define_test "1194") tests;
val () = export_theory_no_docs ();
