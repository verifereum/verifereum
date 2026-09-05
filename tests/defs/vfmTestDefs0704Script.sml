Theory vfmTestDefs0704[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150Specific/call_goes_oog_on_second_level/call_goes_oog_on_second_level.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150Specific/call_goes_oog_on_second_level/call_goes_oog_on_second_level.json");
val defs = mapi (define_test "0704") tests;
