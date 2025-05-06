open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0907Theory;
val () = new_theory "vfmTest0907";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0907") $ get_result_defs "vfmTestDefs0907";
val () = export_theory_no_docs ();
