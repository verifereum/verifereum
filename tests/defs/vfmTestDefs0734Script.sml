open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0734";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionNonce.json";
val defs = mapi (define_test "0734") tests;
val () = export_theory_no_docs ();
