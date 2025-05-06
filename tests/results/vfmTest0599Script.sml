open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0599Theory;
val () = new_theory "vfmTest0599";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0599") $ get_result_defs "vfmTestDefs0599";
val () = export_theory_no_docs ();
