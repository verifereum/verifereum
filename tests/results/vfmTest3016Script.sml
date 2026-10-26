Theory vfmTest3016[no_sig_docs]
Ancestors vfmTestDefs3016
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3016_0.nsv", "result3016_1.nsv", "result3016_2.nsv", "result3016_3.nsv", "result3016_4.nsv", "result3016_5.nsv", "result3016_6.nsv", "result3016_7.nsv", "result3016_8.nsv", "result3016_9.nsv"];
val thyn = "vfmTestDefs3016";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
