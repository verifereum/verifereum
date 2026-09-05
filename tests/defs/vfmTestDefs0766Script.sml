Theory vfmTestDefs0766[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP3860_limitmeterinitcode/create_init_code_size_limit/create_init_code_size_limit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP3860_limitmeterinitcode/create_init_code_size_limit/create_init_code_size_limit.json");
val defs = mapi (define_test "0766") tests;
