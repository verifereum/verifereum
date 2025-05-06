open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0910Theory;
val () = new_theory "vfmTest0910";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0910") $ get_result_defs "vfmTestDefs0910";
val () = export_theory_no_docs ();
