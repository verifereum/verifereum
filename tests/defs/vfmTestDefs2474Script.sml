Theory vfmTestDefs2474[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stTransactionTest/InternalCallStoreClearsSuccess.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stTransactionTest/InternalCallStoreClearsSuccess.json");
val defs = mapi (define_test "2474") tests;
