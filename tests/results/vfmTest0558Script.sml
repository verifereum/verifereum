open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0558Theory;
val () = new_theory "vfmTest0558";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0558") $ get_result_defs "vfmTestDefs0558";
val () = export_theory_no_docs ();
