Theory vfmTestDefs2046[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_mem_oog_and_insufficient_balance/call_to_name_registrator_mem_oog_and_insufficient_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_mem_oog_and_insufficient_balance/call_to_name_registrator_mem_oog_and_insufficient_balance.json");
val defs = mapi (define_test "2046") tests;
