Theory vfmTestDefs0400[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_withdrawing_to_precompiles.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip4895_withdrawals/test_withdrawing_to_precompiles.json");
val defs = mapi (define_test "0400") tests;
