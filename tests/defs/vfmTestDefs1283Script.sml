open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1283";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts/precompsEIP2929Cancun.json";
val defs = mapi (define_test "1283") tests;
val () = export_theory_no_docs ();
