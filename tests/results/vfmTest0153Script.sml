open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0153Theory;
val () = new_theory "vfmTest0153";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0153") $ get_result_defs "vfmTestDefs0153";
val () = export_theory_no_docs ();
