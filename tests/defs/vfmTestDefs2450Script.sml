Theory vfmTestDefs2450[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/shanghai/eip4895_withdrawals/withdrawals/multiple_withdrawals_same_address.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/shanghai/eip4895_withdrawals/withdrawals/multiple_withdrawals_same_address.json");
val defs = mapi (define_test "2450") tests;
