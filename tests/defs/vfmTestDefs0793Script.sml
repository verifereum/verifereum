Theory vfmTestDefs0793[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stInitCodeTest/call_contract_to_create_contract_oog/call_contract_to_create_contract_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stInitCodeTest/call_contract_to_create_contract_oog/call_contract_to_create_contract_oog.json");
val defs = mapi (define_test "0793") tests;
