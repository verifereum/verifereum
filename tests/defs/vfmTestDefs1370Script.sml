open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1370";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallSha256_1_nonzeroValue.json";
val defs = mapi (define_test "1370") tests;
val () = export_theory_no_docs ();
