Theory vfmTestDefs0399[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_withdrawals_root.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip4895_withdrawals/test_withdrawals_root.json");
val defs = mapi (define_test "0399") tests;
