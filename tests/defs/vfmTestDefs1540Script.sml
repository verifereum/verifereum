Theory vfmTestDefs1540[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stInitCodeTest/transaction_create_stop_in_initcode/transaction_create_stop_in_initcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stInitCodeTest/transaction_create_stop_in_initcode/transaction_create_stop_in_initcode.json");
val defs = mapi (define_test "1540") tests;
