open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0305";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/withdrawals/no_evm_execution.json";
val defs = mapi (define_test "0305") tests;
val () = export_theory_no_docs ();
