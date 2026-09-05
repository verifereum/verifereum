Theory vfmTestDefs2447[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/shanghai/eip4895_withdrawals/withdrawals/balance_within_block.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/shanghai/eip4895_withdrawals/withdrawals/balance_within_block.json");
val defs = mapi (define_test "2447") tests;
