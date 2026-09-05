Theory vfmTestDefs2238[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/vmBitwiseLogicOperation/eq/eq.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/vmBitwiseLogicOperation/eq/eq.json");
val defs = mapi (define_test "2238") tests;
