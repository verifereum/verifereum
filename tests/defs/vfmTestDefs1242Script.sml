open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1242";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallIdentity_4_gas18.json";
val defs = mapi (define_test "1242") tests;
val () = export_theory_no_docs ();
