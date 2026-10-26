Theory vfmTestDefs0427[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/eip_vectors/eip_vector_dupn_duplicate_bottom.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/eip_vectors/eip_vector_dupn_duplicate_bottom.json");
val defs = mapi (define_test "0427") tests;
