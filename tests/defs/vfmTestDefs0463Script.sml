Theory vfmTestDefs0463[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/pc_advancement/dupn_multiple_consecutive_pc_advancement.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/pc_advancement/dupn_multiple_consecutive_pc_advancement.json");
val defs = mapi (define_test "0463") tests;
