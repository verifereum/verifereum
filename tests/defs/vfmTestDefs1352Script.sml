open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1352";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallIdentity_2.json";
val defs = mapi (define_test "1352") tests;
val () = export_theory_no_docs ();
