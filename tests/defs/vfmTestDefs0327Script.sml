Theory vfmTestDefs0327[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_system_call_reads/bal_invalid_phantom_read_on_request_predeploy.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_system_call_reads/bal_invalid_phantom_read_on_request_predeploy.json");
val defs = mapi (define_test "0327") tests;
