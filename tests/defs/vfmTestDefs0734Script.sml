Theory vfmTestDefs0734[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1559/out_of_funds/out_of_funds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1559/out_of_funds/out_of_funds.json");
val defs = mapi (define_test "0734") tests;
