open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0739";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionStorageParis.json";
val defs = mapi (define_test "0739") tests;
val () = export_theory_no_docs ();
