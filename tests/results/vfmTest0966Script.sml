open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0966Theory;
val () = new_theory "vfmTest0966";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0966") $ get_result_defs "vfmTestDefs0966";
val () = export_theory_no_docs ();
