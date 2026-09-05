Theory vfmTestDefs0737[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1559/tip_too_high/tip_too_high.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1559/tip_too_high/tip_too_high.json");
val defs = mapi (define_test "0737") tests;
