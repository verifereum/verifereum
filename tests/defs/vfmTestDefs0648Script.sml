Theory vfmTestDefs0648[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_contract_sstore_during_init/create_contract_sstore_during_init.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_contract_sstore_during_init/create_contract_sstore_during_init.json");
val defs = mapi (define_test "0648") tests;
