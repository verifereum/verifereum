Theory vfmTestDefs0617[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2check_fields_in_initcode/create2check_fields_in_initcode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2check_fields_in_initcode/create2check_fields_in_initcode.json");
val defs = mapi (define_test "0617") tests;
