open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0314";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_delegation_clearing_tx_to.json";
val defs = mapi (define_test "0314") tests;
val () = export_theory_no_docs ();
