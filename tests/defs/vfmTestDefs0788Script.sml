Theory vfmTestDefs0788[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_FirstByte_loop.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCreate2/CREATE2_FirstByte_loop.json");
val defs = mapi (define_test "0788") tests;
