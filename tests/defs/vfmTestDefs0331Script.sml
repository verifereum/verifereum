Theory vfmTestDefs0331[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_nonce_overflow_after_first_authorization.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_nonce_overflow_after_first_authorization.json");
val defs = mapi (define_test "0331") tests;
