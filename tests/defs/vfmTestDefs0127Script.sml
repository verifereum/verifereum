open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0127";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_call_large_args_offset_size_zero.json";
val defs = mapi (define_test "0127") tests;
val () = export_theory_no_docs ();
