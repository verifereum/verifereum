open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0774Theory;
val () = new_theory "vfmTest0774";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0774") $ get_result_defs "vfmTestDefs0774";
val () = export_theory_no_docs ();
