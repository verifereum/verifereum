open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2541Theory;
val () = new_theory "vfmTest2541";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2541") $ get_result_defs "vfmTestDefs2541";
val () = export_theory_no_docs ();
