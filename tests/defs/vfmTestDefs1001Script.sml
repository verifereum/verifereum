open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1001";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/valCausesOOF.json";
val defs = mapi (define_test "1001") tests;
val () = export_theory_no_docs ();
