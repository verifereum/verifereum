open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0186Theory;
val () = new_theory "vfmTest0186";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0186") $ get_result_defs "vfmTestDefs0186";
val () = export_theory_no_docs ();
