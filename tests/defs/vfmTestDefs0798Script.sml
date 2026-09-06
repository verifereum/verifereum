Theory vfmTestDefs0798[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stInitCodeTest/call_the_contract_to_create_empty_contract/call_the_contract_to_create_empty_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stInitCodeTest/call_the_contract_to_create_empty_contract/call_the_contract_to_create_empty_contract.json");
val defs = mapi (define_test "0798") tests;
