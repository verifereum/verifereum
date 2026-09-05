Theory vfmTestDefs0650[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_e_contract_create_ne_contract_in_init_oog_tr/create_e_contract_create_ne_contract_in_init_oog_tr.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_e_contract_create_ne_contract_in_init_oog_tr/create_e_contract_create_ne_contract_in_init_oog_tr.json");
val defs = mapi (define_test "0650") tests;
