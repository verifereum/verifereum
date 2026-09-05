Theory vfmTestDefs1991[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_create_contract_suicide_during_init_then_store_then_return/static_create_contract_suicide_during_init_then_store_then_return.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_create_contract_suicide_during_init_then_store_then_return/static_create_contract_suicide_during_init_then_store_then_return.json");
val defs = mapi (define_test "1991") tests;
