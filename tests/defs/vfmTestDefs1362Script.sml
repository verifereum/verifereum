open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1362";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallIdentity_6_inputShorterThanOutput.json";
val defs = mapi (define_test "1362") tests;
val () = export_theory_no_docs ();
