open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0776";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGFromEOARefunds.json";
val defs = mapi (define_test "0776") tests;
val () = export_theory_no_docs ();
