open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2426";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTimeConsuming/static_Call50000_sha256.json";
val defs = mapi (define_test "2426") tests;
val () = export_theory_no_docs ();
