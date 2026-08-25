Theory vfmTestDefs2471[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stTransactionTest/InternalCallHittingGasLimit2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stTransactionTest/InternalCallHittingGasLimit2.json");
val defs = mapi (define_test "2471") tests;
