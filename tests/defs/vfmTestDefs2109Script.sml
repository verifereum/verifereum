Theory vfmTestDefs2109[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/no_src_account1559/no_src_account1559.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/no_src_account1559/no_src_account1559.json");
val defs = mapi (define_test "2109") tests;
