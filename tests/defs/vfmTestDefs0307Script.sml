open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0307";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/withdrawals/use_value_in_contract.json";
val defs = mapi (define_test "0307") tests;
val () = export_theory_no_docs ();
