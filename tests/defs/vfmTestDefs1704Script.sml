Theory vfmTestDefs1704[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stNonZeroCallsTest/non_zero_value_suicide_to_non_non_zero_balance/non_zero_value_suicide_to_non_non_zero_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stNonZeroCallsTest/non_zero_value_suicide_to_non_non_zero_balance/non_zero_value_suicide_to_non_non_zero_balance.json");
val defs = mapi (define_test "1704") tests;
