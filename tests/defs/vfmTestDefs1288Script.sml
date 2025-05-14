open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1288";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts/sec80.json";
val defs = mapi (define_test "1288") tests;
val () = export_theory_no_docs ();
