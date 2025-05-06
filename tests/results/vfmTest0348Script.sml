open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0348Theory;
val () = new_theory "vfmTest0348";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0348") $ get_result_defs "vfmTestDefs0348";
val () = export_theory_no_docs ();
