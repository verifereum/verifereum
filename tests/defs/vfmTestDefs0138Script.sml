open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0138";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_genesis_hash_available.json";
val defs = mapi (define_test "0138") tests;
val () = export_theory_no_docs ();
