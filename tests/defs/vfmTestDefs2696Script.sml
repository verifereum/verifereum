Theory vfmTestDefs2696[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_create_contract_suicide_during_init/static_create_contract_suicide_during_init.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_create_contract_suicide_during_init/static_create_contract_suicide_during_init.json");
val defs = mapi (define_test "2696") tests;
