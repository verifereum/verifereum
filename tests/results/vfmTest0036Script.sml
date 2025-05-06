open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0036Theory;
val () = new_theory "vfmTest0036";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0036") $ get_result_defs "vfmTestDefs0036";
val () = export_theory_no_docs ();
