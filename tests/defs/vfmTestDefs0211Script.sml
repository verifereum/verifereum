Theory vfmTestDefs0211[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/swap/swap.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/swap/swap.json");
val defs = mapi (define_test "0211") tests;
