open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2375";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CreateHashCollision.json";
val defs = mapi (define_test "2375") tests;
val () = export_theory_no_docs ();
