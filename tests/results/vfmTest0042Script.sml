open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0042Theory;
val () = new_theory "vfmTest0042";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0042") $ get_result_defs "vfmTestDefs0042";
val () = export_theory_no_docs ();
