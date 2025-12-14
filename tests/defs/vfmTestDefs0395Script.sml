open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0395";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_no_evm_execution.json";
val defs = mapi (define_test "0395") tests;
val () = export_theory_no_docs ();
