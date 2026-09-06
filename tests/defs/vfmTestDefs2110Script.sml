Theory vfmTestDefs2110[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/no_src_account_create/no_src_account_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/no_src_account_create/no_src_account_create.json");
val defs = mapi (define_test "2110") tests;
