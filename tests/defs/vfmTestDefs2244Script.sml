Theory vfmTestDefs2244[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/vmBitwiseLogicOperation/sgt/sgt.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/vmBitwiseLogicOperation/sgt/sgt.json");
val defs = mapi (define_test "2244") tests;
