Theory vfmTestDefs0393[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_multiple_withdrawals_same_address.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip4895_withdrawals/test_multiple_withdrawals_same_address.json");
val defs = mapi (define_test "0393") tests;
