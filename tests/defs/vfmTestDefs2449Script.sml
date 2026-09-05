Theory vfmTestDefs2449[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/shanghai/eip4895_withdrawals/withdrawals/many_withdrawals.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/shanghai/eip4895_withdrawals/withdrawals/many_withdrawals.json");
val defs = mapi (define_test "2449") tests;
