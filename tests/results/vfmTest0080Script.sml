open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0080Theory;
val () = new_theory "vfmTest0080";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0080") $ get_result_defs "vfmTestDefs0080";
val () = export_theory_no_docs ();
