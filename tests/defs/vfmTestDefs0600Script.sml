Theory vfmTestDefs0600[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2_contract_suicide_during_init_then_store_then_return/create2_contract_suicide_during_init_then_store_then_return.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2_contract_suicide_during_init_then_store_then_return/create2_contract_suicide_during_init_then_store_then_return.json");
val defs = mapi (define_test "0600") tests;
