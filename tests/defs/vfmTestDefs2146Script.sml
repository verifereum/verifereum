open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2146";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CheckOpcodes4.json";
val defs = mapi (define_test "2146") tests;
val () = export_theory_no_docs ();
