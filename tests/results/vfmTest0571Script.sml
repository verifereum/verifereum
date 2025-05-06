open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0571Theory;
val () = new_theory "vfmTest0571";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0571") $ get_result_defs "vfmTestDefs0571";
val () = export_theory_no_docs ();
