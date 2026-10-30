Theory vfmTestDefs1537[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stInitCodeTest/stack_under_flow_contract_creation/stack_under_flow_contract_creation.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stInitCodeTest/stack_under_flow_contract_creation/stack_under_flow_contract_creation.json");
val defs = mapi (define_test "1537") tests;
