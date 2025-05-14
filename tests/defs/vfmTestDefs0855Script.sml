open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0855";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionSelfdestructedRevert.json";
val defs = mapi (define_test "0855") tests;
val () = export_theory_no_docs ();
