open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0578Theory;
val () = new_theory "vfmTest0578";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0578") $ get_result_defs "vfmTestDefs0578";
val () = export_theory_no_docs ();
