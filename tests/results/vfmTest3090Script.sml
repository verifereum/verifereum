Theory vfmTest3090[no_sig_docs]
Ancestors vfmTestDefs3090
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3090_0.nsv", "result3090_1.nsv", "result3090_2.nsv", "result3090_3.nsv", "result3090_4.nsv", "result3090_5.nsv", "result3090_6.nsv", "result3090_7.nsv"];
val thyn = "vfmTestDefs3090";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
