Theory vfmTestDefs0380[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_valid_tx_invalid_auth_signature.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_valid_tx_invalid_auth_signature.json");
val defs = mapi (define_test "0380") tests;
