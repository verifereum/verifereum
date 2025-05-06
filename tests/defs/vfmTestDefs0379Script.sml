open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0379";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmLogTest/log2.json";
val defs = mapi (define_test "0379") tests;
val () = export_theory_no_docs ();
