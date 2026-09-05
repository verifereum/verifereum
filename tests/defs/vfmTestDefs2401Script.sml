Theory vfmTestDefs2401[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs/set_code_to_non_empty_storage_non_zero_nonce.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs/set_code_to_non_empty_storage_non_zero_nonce.json");
val defs = mapi (define_test "2401") tests;
