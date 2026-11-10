Theory vfmTest3148[no_sig_docs]
Ancestors vfmTestDefs3148
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3148_0.nsv", "result3148_1.nsv", "result3148_2.nsv", "result3148_3.nsv"];
val thyn = "vfmTestDefs3148";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
