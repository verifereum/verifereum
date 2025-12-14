open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0103";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_recreate_self_destructed_contract_different_txs.json";
val defs = mapi (define_test "0103") tests;
val () = export_theory_no_docs ();
