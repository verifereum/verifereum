Theory vfmTestDefs0708[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150Specific/suicide_to_existing_contract/suicide_to_existing_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150Specific/suicide_to_existing_contract/suicide_to_existing_contract.json");
val defs = mapi (define_test "0708") tests;
