Theory vfmTestDefs0003[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/berlin/eip2930_access_list/test_eip2930_tx_validity.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/berlin/eip2930_access_list/test_eip2930_tx_validity.json");
val defs = mapi (define_test "0003") tests;
