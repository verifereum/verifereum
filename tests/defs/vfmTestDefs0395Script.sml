Theory vfmTestDefs0395[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_no_evm_execution.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip4895_withdrawals/test_no_evm_execution.json");
val defs = mapi (define_test "0395") tests;
