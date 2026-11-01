Theory vfmTestDefs0236[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7702/bal_7702_delegated_via_call_opcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/block_access_lists_eip7702/bal_7702_delegated_via_call_opcode.json");
val defs = mapi (define_test "0236") tests;
