Theory vfmTestDefs1990[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_create_contract_suicide_during_init/static_create_contract_suicide_during_init.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_create_contract_suicide_during_init/static_create_contract_suicide_during_init.json");
val defs = mapi (define_test "1990") tests;
