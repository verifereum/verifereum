Theory vfmTestDefs1786[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_contract_to_create_contract_oog/static_call_contract_to_create_contract_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_contract_to_create_contract_oog/static_call_contract_to_create_contract_oog.json");
val defs = mapi (define_test "1786") tests;
