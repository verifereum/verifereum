Theory vfmTest0309[no_sig_docs]
Ancestors vfmTestDefs0309
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0309_0.nsv", "result0309_1.nsv", "result0309_2.nsv", "result0309_3.nsv"];
val thyn = "vfmTestDefs0309";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
