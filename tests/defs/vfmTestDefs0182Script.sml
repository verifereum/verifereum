Theory vfmTestDefs0182[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/eip2681_limit_account_nonce/nonce_reaching_max/tx_at_nonce_max_minus_one_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/eip2681_limit_account_nonce/nonce_reaching_max/tx_at_nonce_max_minus_one_create.json");
val defs = mapi (define_test "0182") tests;
