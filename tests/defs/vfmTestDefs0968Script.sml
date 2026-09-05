Theory vfmTestDefs0968[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stNonZeroCallsTest/non_zero_value_suicide_to_empty_paris/non_zero_value_suicide_to_empty_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stNonZeroCallsTest/non_zero_value_suicide_to_empty_paris/non_zero_value_suicide_to_empty_paris.json");
val defs = mapi (define_test "0968") tests;
