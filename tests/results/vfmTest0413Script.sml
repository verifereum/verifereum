open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0413Theory;
val () = new_theory "vfmTest0413";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0413") $ get_result_defs "vfmTestDefs0413";
val () = export_theory_no_docs ();
