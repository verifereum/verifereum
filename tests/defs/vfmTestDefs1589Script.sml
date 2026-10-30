Theory vfmTestDefs1589[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemExpandingEIP150Calls/delegate_call_on_eip_with_mem_expanding_calls/delegate_call_on_eip_with_mem_expanding_calls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemExpandingEIP150Calls/delegate_call_on_eip_with_mem_expanding_calls/delegate_call_on_eip_with_mem_expanding_calls.json");
val defs = mapi (define_test "1589") tests;
