Theory vfmTestDefs1680[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_gas_left/sstore_gas_left.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_gas_left/sstore_gas_left.json");
val defs = mapi (define_test "1680") tests;
