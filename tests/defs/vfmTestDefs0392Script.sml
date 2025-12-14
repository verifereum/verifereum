open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0392";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_many_withdrawals.json";
val defs = mapi (define_test "0392") tests;
val () = export_theory_no_docs ();
