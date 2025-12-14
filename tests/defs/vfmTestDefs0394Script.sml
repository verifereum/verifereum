open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0394";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_newly_created_contract.json";
val defs = mapi (define_test "0394") tests;
val () = export_theory_no_docs ();
