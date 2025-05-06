open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2755Theory;
val () = new_theory "vfmTest2755";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2755") $ get_result_defs "vfmTestDefs2755";
val () = export_theory_no_docs ();
