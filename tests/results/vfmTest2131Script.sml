open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2131Theory;
val () = new_theory "vfmTest2131";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2131") $ get_result_defs "vfmTestDefs2131";
val () = export_theory_no_docs ();
