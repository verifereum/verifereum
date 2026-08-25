Theory vfmTestDefs2400[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorMemOOGAndInsufficientBalance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorMemOOGAndInsufficientBalance.json");
val defs = mapi (define_test "2400") tests;
