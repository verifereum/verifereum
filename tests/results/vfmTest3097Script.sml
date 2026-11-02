Theory vfmTest3097[no_sig_docs]
Ancestors vfmTestDefs3097
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3097_0.nsv", "result3097_1.nsv", "result3097_2.nsv", "result3097_3.nsv", "result3097_4.nsv", "result3097_5.nsv", "result3097_6.nsv", "result3097_7.nsv", "result3097_8.nsv", "result3097_9.nsv"];
val thyn = "vfmTestDefs3097";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
