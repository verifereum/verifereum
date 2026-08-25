Theory vfmTestDefs0126[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/opcodes/test_all_opcodes.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/opcodes/test_all_opcodes.json");
val defs = mapi (define_test "0126") tests;
