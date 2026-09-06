Theory vfmTestDefs0180[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/eip2681_limit_account_nonce/nonce_reaching_max/set_code_self_authorization_reaching_nonce_max.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/eip2681_limit_account_nonce/nonce_reaching_max/set_code_self_authorization_reaching_nonce_max.json");
val defs = mapi (define_test "0180") tests;
