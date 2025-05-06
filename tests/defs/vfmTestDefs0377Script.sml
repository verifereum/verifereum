open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0377";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmLogTest/log0.json";
val defs = mapi (define_test "0377") tests;
val () = export_theory_no_docs ();
