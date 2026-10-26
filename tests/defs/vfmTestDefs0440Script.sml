Theory vfmTestDefs0440[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/eip_vectors/vector_exchange_0x2f.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/eip_vectors/vector_exchange_0x2f.json");
val defs = mapi (define_test "0440") tests;
