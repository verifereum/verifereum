open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0749Theory;
val () = new_theory "vfmTest0749";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0749") $ get_result_defs "vfmTestDefs0749";
val () = export_theory_no_docs ();
