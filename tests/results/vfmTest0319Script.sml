open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0319Theory;
val () = new_theory "vfmTest0319";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0319") $ get_result_defs "vfmTestDefs0319";
val () = export_theory_no_docs ();
