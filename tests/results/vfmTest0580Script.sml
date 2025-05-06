open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0580Theory;
val () = new_theory "vfmTest0580";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0580") $ get_result_defs "vfmTestDefs0580";
val () = export_theory_no_docs ();
