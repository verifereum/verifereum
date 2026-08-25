Theory vfmTestDefs2470[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stTransactionTest/InternalCallHittingGasLimit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stTransactionTest/InternalCallHittingGasLimit.json");
val defs = mapi (define_test "2470") tests;
