Theory vfmTestDefs0357[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_multiple_valid_authorization_tuples_same_signer_increasing_nonce_self_sponsored.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_set_code_multiple_valid_authorization_tuples_same_signer_increasing_nonce_self_sponsored.json");
val defs = mapi (define_test "0357") tests;
