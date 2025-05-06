open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0742Theory;
val () = new_theory "vfmTest0742";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0742") $ get_result_defs "vfmTestDefs0742";
val () = export_theory_no_docs ();
