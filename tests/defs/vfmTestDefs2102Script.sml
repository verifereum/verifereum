Theory vfmTestDefs2102[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/high_gas_price_paris/high_gas_price_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/high_gas_price_paris/high_gas_price_paris.json");
val defs = mapi (define_test "2102") tests;
