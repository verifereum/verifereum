open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1253";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallRipemd160_5.json";
val defs = mapi (define_test "1253") tests;
val () = export_theory_no_docs ();
