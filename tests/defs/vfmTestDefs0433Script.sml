Theory vfmTestDefs0433[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/eip_vectors/eip_vector_exchange_with_iszero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/eip_vectors/eip_vector_exchange_with_iszero.json");
val defs = mapi (define_test "0433") tests;
