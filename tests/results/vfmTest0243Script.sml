open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0243Theory;
val () = new_theory "vfmTest0243";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0243") $ get_result_defs "vfmTestDefs0243";
val () = export_theory_no_docs ();
