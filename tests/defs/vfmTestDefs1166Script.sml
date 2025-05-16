open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1166";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts/identity_to_smaller.json";
val defs = mapi (define_test "1166") tests;
val () = export_theory_no_docs ();
