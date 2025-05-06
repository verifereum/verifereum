open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0752Theory;
val () = new_theory "vfmTest0752";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0752") $ get_result_defs "vfmTestDefs0752";
val () = export_theory_no_docs ();
