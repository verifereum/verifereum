Theory vfmTestDefs0118[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7843_slotnum/slotnum/slotnum_stack_overflow.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7843_slotnum/slotnum/slotnum_stack_overflow.json");
val defs = mapi (define_test "0118") tests;
