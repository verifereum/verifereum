Theory vfmTest3114[no_sig_docs]
Ancestors vfmTestDefs3114
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3114_0.nsv", "result3114_1.nsv", "result3114_2.nsv", "result3114_3.nsv", "result3114_4.nsv", "result3114_5.nsv", "result3114_6.nsv", "result3114_7.nsv"];
val thyn = "vfmTestDefs3114";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
