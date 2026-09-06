Theory vfmTestDefs0236[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/london/validation/header/invalid_header.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/london/validation/header/invalid_header.json");
val defs = mapi (define_test "0236") tests;
