Theory vfmTest0053[no_sig_docs]
Ancestors vfmTestDefs0053
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0053_0.nsv", "result0053_1.nsv"];
val thyn = "vfmTestDefs0053";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
