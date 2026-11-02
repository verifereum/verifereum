Theory vfmTestDefs1526[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stInitCodeTest/call_contract_to_create_contract_no_cash/call_contract_to_create_contract_no_cash.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stInitCodeTest/call_contract_to_create_contract_no_cash/call_contract_to_create_contract_no_cash.json");
val defs = mapi (define_test "1526") tests;
