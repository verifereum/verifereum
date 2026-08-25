Theory vfmTestDefs2010[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^255-1_256.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stShift/sar_2^255-1_256.json");
val defs = mapi (define_test "2010") tests;
