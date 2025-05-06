open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1789Theory;
val () = new_theory "vfmTest1789";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1789") $ get_result_defs "vfmTestDefs1789";
val () = export_theory_no_docs ();
