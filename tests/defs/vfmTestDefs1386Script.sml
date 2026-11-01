Theory vfmTestDefs1386[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCreateTest/create_contract_return_big_offset/create_contract_return_big_offset.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCreateTest/create_contract_return_big_offset/create_contract_return_big_offset.json");
val defs = mapi (define_test "1386") tests;
