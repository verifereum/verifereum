open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0541Theory;
val () = new_theory "vfmTest0541";
val thyn = "vfmTestDefs0541";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
