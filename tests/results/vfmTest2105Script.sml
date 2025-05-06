open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2105Theory;
val () = new_theory "vfmTest2105";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2105") $ get_result_defs "vfmTestDefs2105";
val () = export_theory_no_docs ();
