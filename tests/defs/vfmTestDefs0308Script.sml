open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0308";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_contract_storage_to_pointer_with_storage.json";
val defs = mapi (define_test "0308") tests;
val () = export_theory_no_docs ();
