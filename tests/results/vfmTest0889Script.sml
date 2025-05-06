open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0889Theory;
val () = new_theory "vfmTest0889";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0889") $ get_result_defs "vfmTestDefs0889";
val () = export_theory_no_docs ();
