open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0735Theory;
val () = new_theory "vfmTest0735";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0735") $ get_result_defs "vfmTestDefs0735";
val () = export_theory_no_docs ();
