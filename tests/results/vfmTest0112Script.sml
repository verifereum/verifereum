open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0112Theory;
val () = new_theory "vfmTest0112";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0112") $ get_result_defs "vfmTestDefs0112";
val () = export_theory_no_docs ();
