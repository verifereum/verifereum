Theory vfmTestDefs2191[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stZeroCallsRevert/zero_value_suicide_to_one_storage_key_oog_revert_paris/zero_value_suicide_to_one_storage_key_oog_revert_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stZeroCallsRevert/zero_value_suicide_to_one_storage_key_oog_revert_paris/zero_value_suicide_to_one_storage_key_oog_revert_paris.json");
val defs = mapi (define_test "2191") tests;
