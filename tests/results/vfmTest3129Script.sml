Theory vfmTest3129[no_sig_docs]
Ancestors vfmTestDefs3129
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3129_0.nsv", "result3129_1.nsv", "result3129_2.nsv", "result3129_3.nsv", "result3129_4.nsv", "result3129_5.nsv", "result3129_6.nsv", "result3129_7.nsv", "result3129_8.nsv", "result3129_9.nsv", "result3129_10.nsv", "result3129_11.nsv"];
val thyn = "vfmTestDefs3129";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
