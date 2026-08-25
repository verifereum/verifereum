Theory vfmTestDefs0372[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_transaction_fee_validations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_set_code_transaction_fee_validations.json");
val defs = mapi (define_test "0372") tests;
