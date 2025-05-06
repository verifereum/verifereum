open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0541Theory;
val () = new_theory "vfmTest0541";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0541") $ get_result_defs "vfmTestDefs0541";
val () = export_theory_no_docs ();
