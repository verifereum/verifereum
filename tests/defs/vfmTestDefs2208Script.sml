Theory vfmTestDefs2208[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stZeroCallsTest/zero_value_transaction_cal_lwith_data/zero_value_transaction_cal_lwith_data.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stZeroCallsTest/zero_value_transaction_cal_lwith_data/zero_value_transaction_cal_lwith_data.json");
val defs = mapi (define_test "2208") tests;
