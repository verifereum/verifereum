Theory vfmTestDefs1081[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/opcodes/exp/gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/opcodes/exp/gas.json");
val defs = mapi (define_test "1081") tests;
