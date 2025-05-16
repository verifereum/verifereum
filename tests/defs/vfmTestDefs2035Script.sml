open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2035";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/sha3_deja.json";
val defs = mapi (define_test "2035") tests;
val () = export_theory_no_docs ();
