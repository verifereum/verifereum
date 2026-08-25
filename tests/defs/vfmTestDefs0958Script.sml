Theory vfmTestDefs0958[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP1559/baseFeeDiffPlaces.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP1559/baseFeeDiffPlaces.json");
val defs = mapi (define_test "0958") tests;
