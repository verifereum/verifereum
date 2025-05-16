open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2423";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTimeConsuming/sstore_combinations_initial20_Paris.json";
val defs = mapi (define_test "2423") tests;
val () = export_theory_no_docs ();
