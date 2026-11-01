Theory vfmTestDefs0453[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/exchange/exchange_invalid_immediate_aborts.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8024_dupn_swapn_exchange/exchange/exchange_invalid_immediate_aborts.json");
val defs = mapi (define_test "0453") tests;
