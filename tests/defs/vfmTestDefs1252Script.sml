open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1252";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallRipemd160_4_gas719.json";
val defs = mapi (define_test "1252") tests;
val () = export_theory_no_docs ();
