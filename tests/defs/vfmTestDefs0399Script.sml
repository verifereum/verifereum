open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0399";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_withdrawals_root.json";
val defs = mapi (define_test "0399") tests;
val () = export_theory_no_docs ();
