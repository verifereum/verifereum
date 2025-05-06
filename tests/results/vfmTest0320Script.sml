open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0320Theory;
val () = new_theory "vfmTest0320";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0320") $ get_result_defs "vfmTestDefs0320";
val () = export_theory_no_docs ();
