Theory vfmTestDefs1539[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stInitCodeTest/transaction_create_random_init_code/transaction_create_random_init_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stInitCodeTest/transaction_create_random_init_code/transaction_create_random_init_code.json");
val defs = mapi (define_test "1539") tests;
