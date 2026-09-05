Theory vfmTestDefs0229[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/istanbul/eip152_blake2/blake2/blake2b_invalid_input.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/istanbul/eip152_blake2/blake2/blake2b_invalid_input.json");
val defs = mapi (define_test "0229") tests;
