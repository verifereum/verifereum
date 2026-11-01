Theory vfmTestDefs2461[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stSolidityTest/test_block_and_transaction_properties/test_block_and_transaction_properties.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stSolidityTest/test_block_and_transaction_properties/test_block_and_transaction_properties.json");
val defs = mapi (define_test "2461") tests;
