open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0801Theory;
val () = new_theory "vfmTest0801";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0801") $ get_result_defs "vfmTestDefs0801";
val () = export_theory_no_docs ();
