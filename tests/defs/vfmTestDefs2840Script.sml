Theory vfmTestDefs2840[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stWalletTest/day_limit_construction/day_limit_construction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stWalletTest/day_limit_construction/day_limit_construction.json");
val defs = mapi (define_test "2840") tests;
