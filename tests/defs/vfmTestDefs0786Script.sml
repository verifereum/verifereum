Theory vfmTestDefs0786[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stHomesteadSpecific/contract_creation_oo_gdont_leave_empty_contract/contract_creation_oo_gdont_leave_empty_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stHomesteadSpecific/contract_creation_oo_gdont_leave_empty_contract/contract_creation_oo_gdont_leave_empty_contract.json");
val defs = mapi (define_test "0786") tests;
