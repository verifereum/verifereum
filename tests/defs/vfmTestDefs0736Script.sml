open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0736";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionSelfdestructed2.json";
val defs = mapi (define_test "0736") tests;
val () = export_theory_no_docs ();
