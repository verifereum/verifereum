Theory vfmTestDefs0788[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stHomesteadSpecific/create_contract_via_contract/create_contract_via_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stHomesteadSpecific/create_contract_via_contract/create_contract_via_contract.json");
val defs = mapi (define_test "0788") tests;
