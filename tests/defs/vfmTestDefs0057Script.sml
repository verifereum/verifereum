Theory vfmTestDefs0057[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage_selfdestruct/reentrant_selfdestructing_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage_selfdestruct/reentrant_selfdestructing_call.json");
val defs = mapi (define_test "0057") tests;
