Theory vfmTestDefs0444[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/and.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/and.json");
val defs = mapi (define_test "0444") tests;
