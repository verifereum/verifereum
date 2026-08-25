Theory vfmTestDefs2403[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorOutOfGas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorOutOfGas.json");
val defs = mapi (define_test "2403") tests;
