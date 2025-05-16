open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0878";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/lowFeeCap.json";
val defs = mapi (define_test "0878") tests;
val () = export_theory_no_docs ();
