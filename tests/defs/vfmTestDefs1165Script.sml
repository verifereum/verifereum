open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1165";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts/identity_to_bigger.json";
val defs = mapi (define_test "1165") tests;
val () = export_theory_no_docs ();
