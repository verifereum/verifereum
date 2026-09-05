Theory vfmTestDefs1749[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSolidityTest/test_contract_interaction/test_contract_interaction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSolidityTest/test_contract_interaction/test_contract_interaction.json");
val defs = mapi (define_test "1749") tests;
