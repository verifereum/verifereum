open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0946Theory;
val () = new_theory "vfmTest0946";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0946") $ get_result_defs "vfmTestDefs0946";
val () = export_theory_no_docs ();
