Theory vfmTestDefs0352[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_from_account_with_non_delegating_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_set_code_from_account_with_non_delegating_code.json");
val defs = mapi (define_test "0352") tests;
