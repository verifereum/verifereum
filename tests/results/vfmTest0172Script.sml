open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0172Theory;
val () = new_theory "vfmTest0172";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0172") $ get_result_defs "vfmTestDefs0172";
val () = export_theory_no_docs ();
