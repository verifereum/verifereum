Theory vfmTest0209[no_sig_docs]
Ancestors vfmTestDefs0209
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0209_0.nsv", "result0209_1.nsv", "result0209_2.nsv", "result0209_3.nsv", "result0209_4.nsv", "result0209_5.nsv", "result0209_6.nsv", "result0209_7.nsv", "result0209_8.nsv", "result0209_9.nsv", "result0209_10.nsv", "result0209_11.nsv", "result0209_12.nsv", "result0209_13.nsv", "result0209_14.nsv", "result0209_15.nsv"];
val thyn = "vfmTestDefs0209";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
