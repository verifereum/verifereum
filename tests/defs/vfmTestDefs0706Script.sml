Theory vfmTestDefs0706[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150Specific/delegate_call_on_eip/delegate_call_on_eip.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150Specific/delegate_call_on_eip/delegate_call_on_eip.json");
val defs = mapi (define_test "0706") tests;
