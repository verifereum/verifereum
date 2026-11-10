Theory vfmTestDefs0899[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/byzantium/eip211_return_data/call/call_clears_return_data_on_insufficient_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/byzantium/eip211_return_data/call/call_clears_return_data_on_insufficient_balance.json");
val defs = mapi (define_test "0899") tests;
