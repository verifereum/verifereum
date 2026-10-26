Theory vfmTestDefs3157[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/shanghai/eip4895_withdrawals/withdrawals/large_amount.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/shanghai/eip4895_withdrawals/withdrawals/large_amount.json");
val defs = mapi (define_test "3157") tests;
