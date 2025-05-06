open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0444Theory;
val () = new_theory "vfmTest0444";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0444") $ get_result_defs "vfmTestDefs0444";
val () = export_theory_no_docs ();
