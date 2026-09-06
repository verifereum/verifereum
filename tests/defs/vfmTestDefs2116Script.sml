Theory vfmTestDefs2116[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/store_gas_on_create/store_gas_on_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/store_gas_on_create/store_gas_on_create.json");
val defs = mapi (define_test "2116") tests;
