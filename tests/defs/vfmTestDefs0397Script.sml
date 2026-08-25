Theory vfmTestDefs0397[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_use_value_in_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip4895_withdrawals/test_use_value_in_contract.json");
val defs = mapi (define_test "0397") tests;
