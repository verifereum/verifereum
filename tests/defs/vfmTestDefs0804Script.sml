Theory vfmTestDefs0804[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stInitCodeTest/transaction_create_auto_suicide_contract/transaction_create_auto_suicide_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stInitCodeTest/transaction_create_auto_suicide_contract/transaction_create_auto_suicide_contract.json");
val defs = mapi (define_test "0804") tests;
