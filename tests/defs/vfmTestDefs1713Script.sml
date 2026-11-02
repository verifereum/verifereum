Theory vfmTestDefs1713[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stNonZeroCallsTest/non_zero_value_transaction_call_to_one_storage_key_paris/non_zero_value_transaction_call_to_one_storage_key_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stNonZeroCallsTest/non_zero_value_transaction_call_to_one_storage_key_paris/non_zero_value_transaction_call_to_one_storage_key_paris.json");
val defs = mapi (define_test "1713") tests;
