Theory vfmTestDefs2100[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/empty_transaction3/empty_transaction3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/empty_transaction3/empty_transaction3.json");
val defs = mapi (define_test "2100") tests;
