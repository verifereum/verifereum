open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0500Theory;
val () = new_theory "vfmTest0500";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0500") $ get_result_defs "vfmTestDefs0500";
val () = export_theory_no_docs ();
