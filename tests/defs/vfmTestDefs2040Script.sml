Theory vfmTestDefs2040[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/balance_input_address_too_big/balance_input_address_too_big.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/balance_input_address_too_big/balance_input_address_too_big.json");
val defs = mapi (define_test "2040") tests;
