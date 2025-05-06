open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1282";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts/modexpTests.json";
val defs = mapi (define_test "1282") tests;
val () = export_theory_no_docs ();
