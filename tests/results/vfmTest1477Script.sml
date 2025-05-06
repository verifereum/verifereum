open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1477Theory;
val () = new_theory "vfmTest1477";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1477") $ get_result_defs "vfmTestDefs1477";
val () = export_theory_no_docs ();
