open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2040";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/costRevert.json";
val defs = mapi (define_test "2040") tests;
val () = export_theory_no_docs ();
