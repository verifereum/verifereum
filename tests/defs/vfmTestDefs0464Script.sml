Theory vfmTestDefs0464[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/pc_advancement/dupn_pc_advances_by_2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/pc_advancement/dupn_pc_advances_by_2.json");
val defs = mapi (define_test "0464") tests;
