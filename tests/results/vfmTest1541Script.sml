open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1541Theory;
val () = new_theory "vfmTest1541";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1541") $ get_result_defs "vfmTestDefs1541";
val () = export_theory_no_docs ();
