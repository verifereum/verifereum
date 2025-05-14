open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1358";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallIdentity_4.json";
val defs = mapi (define_test "1358") tests;
val () = export_theory_no_docs ();
