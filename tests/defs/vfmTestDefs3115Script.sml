Theory vfmTestDefs3115[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip7702_set_code_tx/set_code_txs/set_code_to_self_destructing_account_deployed_in_same_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip7702_set_code_tx/set_code_txs/set_code_to_self_destructing_account_deployed_in_same_tx.json");
val defs = mapi (define_test "3115") tests;
