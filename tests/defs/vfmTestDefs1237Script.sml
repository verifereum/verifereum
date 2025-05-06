open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1237";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/memCopySelf.json";
val defs = mapi (define_test "1237") tests;
val () = export_theory_no_docs ();
