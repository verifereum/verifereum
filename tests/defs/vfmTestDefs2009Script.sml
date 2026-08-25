Theory vfmTestDefs2009[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^255-1_255.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stShift/sar_2^255-1_255.json");
val defs = mapi (define_test "2009") tests;
