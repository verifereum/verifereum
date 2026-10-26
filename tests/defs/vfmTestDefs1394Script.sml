Theory vfmTestDefs1394[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCreateTest/create_empty_contract_with_storage/create_empty_contract_with_storage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCreateTest/create_empty_contract_with_storage/create_empty_contract_with_storage.json");
val defs = mapi (define_test "1394") tests;
