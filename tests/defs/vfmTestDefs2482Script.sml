Theory vfmTestDefs2482[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stTransactionTest/StoreClearsAndInternalCallStoreClearsOOG.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stTransactionTest/StoreClearsAndInternalCallStoreClearsOOG.json");
val defs = mapi (define_test "2482") tests;
