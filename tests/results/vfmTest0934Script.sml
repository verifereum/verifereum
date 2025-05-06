open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0934Theory;
val () = new_theory "vfmTest0934";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0934") $ get_result_defs "vfmTestDefs0934";
val () = export_theory_no_docs ();
