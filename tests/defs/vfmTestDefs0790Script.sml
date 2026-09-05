Theory vfmTestDefs0790[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stHomesteadSpecific/create_contract_via_transaction_cost53000/create_contract_via_transaction_cost53000.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stHomesteadSpecific/create_contract_via_transaction_cost53000/create_contract_via_transaction_cost53000.json");
val defs = mapi (define_test "0790") tests;
