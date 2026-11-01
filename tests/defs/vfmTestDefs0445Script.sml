Theory vfmTestDefs0445[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/eip_vectors/vector_push_in_immediate_masks_jumpdest.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/eip_vectors/vector_push_in_immediate_masks_jumpdest.json");
val defs = mapi (define_test "0445") tests;
