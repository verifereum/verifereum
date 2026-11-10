Theory vfmTestDefs1059[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/examples/block_intermediate_state/block_intermediate_state.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/examples/block_intermediate_state/block_intermediate_state.json");
val defs = mapi (define_test "1059") tests;
