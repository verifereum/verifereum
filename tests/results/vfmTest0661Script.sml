Theory vfmTest0661[no_sig_docs]
Ancestors vfmTestDefs0661
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0661_0.nsv", "result0661_1.nsv"];
val thyn = "vfmTestDefs0661";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
