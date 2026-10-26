Theory vfmTestDefs0423[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/dupn/dupn_valid_immediates.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/dupn/dupn_valid_immediates.json");
val defs = mapi (define_test "0423") tests;
