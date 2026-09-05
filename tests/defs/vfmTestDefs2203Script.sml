Theory vfmTestDefs2203[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stZeroCallsTest/zero_value_delegatecall_to_one_storage_key_paris/zero_value_delegatecall_to_one_storage_key_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stZeroCallsTest/zero_value_delegatecall_to_one_storage_key_paris/zero_value_delegatecall_to_one_storage_key_paris.json");
val defs = mapi (define_test "2203") tests;
