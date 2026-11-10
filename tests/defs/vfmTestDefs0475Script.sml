Theory vfmTestDefs0475[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/swapn/swapn_jump_to_valid_immediate_fails.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/swapn/swapn_jump_to_valid_immediate_fails.json");
val defs = mapi (define_test "0475") tests;
