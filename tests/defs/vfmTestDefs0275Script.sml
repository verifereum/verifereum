open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0275";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs_2/contract_storage_to_pointer_with_storage.json";
val defs = mapi (define_test "0275") tests;
val () = export_theory_no_docs ();
