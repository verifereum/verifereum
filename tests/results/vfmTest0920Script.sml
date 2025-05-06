open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0920Theory;
val () = new_theory "vfmTest0920";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0920") $ get_result_defs "vfmTestDefs0920";
val () = export_theory_no_docs ();
