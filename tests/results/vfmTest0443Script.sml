open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0443Theory;
val () = new_theory "vfmTest0443";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0443") $ get_result_defs "vfmTestDefs0443";
val () = export_theory_no_docs ();
