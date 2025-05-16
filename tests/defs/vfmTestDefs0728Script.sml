open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0728";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/create2SmartInitCode.json";
val defs = mapi (define_test "0728") tests;
val () = export_theory_no_docs ();
