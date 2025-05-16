open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0767";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_FirstByte_loop.json";
val defs = mapi (define_test "0767") tests;
val () = export_theory_no_docs ();
