open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0431Theory;
val () = new_theory "vfmTest0431";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0431") $ get_result_defs "vfmTestDefs0431";
val () = export_theory_no_docs ();
