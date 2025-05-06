open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0161Theory;
val () = new_theory "vfmTest0161";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0161") $ get_result_defs "vfmTestDefs0161";
val () = export_theory_no_docs ();
