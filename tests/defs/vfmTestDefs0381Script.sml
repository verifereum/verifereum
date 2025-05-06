open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0381";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmLogTest/log4.json";
val defs = mapi (define_test "0381") tests;
val () = export_theory_no_docs ();
