open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0424Theory;
val () = new_theory "vfmTest0424";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0424") $ get_result_defs "vfmTestDefs0424";
val () = export_theory_no_docs ();
