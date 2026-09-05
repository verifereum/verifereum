Theory vfmTestDefs0807[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stInitCodeTest/transaction_create_suicide_in_initcode/transaction_create_suicide_in_initcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stInitCodeTest/transaction_create_suicide_in_initcode/transaction_create_suicide_in_initcode.json");
val defs = mapi (define_test "0807") tests;
