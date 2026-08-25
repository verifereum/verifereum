Theory vfmTestDefs2466[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stTransactionTest/CreateTransactionSuccess.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stTransactionTest/CreateTransactionSuccess.json");
val defs = mapi (define_test "2466") tests;
