open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0891";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateCollisionToEmpty2.json";
val defs = mapi (define_test "0891") tests;
val () = export_theory_no_docs ();
