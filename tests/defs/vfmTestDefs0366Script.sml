Theory vfmTestDefs0366[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_self_destructing_account_deployed_in_same_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_self_destructing_account_deployed_in_same_tx.json");
val defs = mapi (define_test "0366") tests;
