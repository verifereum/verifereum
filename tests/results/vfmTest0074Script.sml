open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0074Theory;
val () = new_theory "vfmTest0074";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0074") $ get_result_defs "vfmTestDefs0074";
val () = export_theory_no_docs ();
