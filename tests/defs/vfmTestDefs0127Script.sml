open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0127";
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip152_blake2/blake2/blake2b.json";
val defs = mapi (define_test "0127") tests;
val () = export_theory_no_docs ();
