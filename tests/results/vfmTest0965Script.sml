open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0965Theory;
val () = new_theory "vfmTest0965";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0965") $ get_result_defs "vfmTestDefs0965";
val () = export_theory_no_docs ();
